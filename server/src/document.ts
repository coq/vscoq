'use strict';

import * as util from 'util';
import {ITextDocument, TextDocumentContentChangeEvent, RemoteConsole, Position, Range, Diagnostic, DiagnosticSeverity} from 'vscode-languageserver';
import {CoqTop, FailureResult, AddResult, EditAtResult, GoalResult} from './coqtop';
import * as thmProto from './protocol';
import * as coqProto from './coq-proto';
import * as coqParser from './coq-parser';
import {Sentence, Sentences} from './sentences';
import * as textUtil from './text-util';
import {Mutex} from './Mutex';
import {CancellationSignal, asyncWithTimeout} from './CancellationSignal';
import {AsyncWorkQueue} from './AsyncQueue';

function rangeToString(r:Range) {return `[${positionToString(r.start)},${positionToString(r.end)})`}
function positionToString(p:Position) {return `{${p.line}@${p.character}}`}


export interface DocumentCallbacks {
  sendHighlightUpdates(highlights: thmProto.Highlight[]) : void;
  sendDiagnostics(diagnostics: Diagnostic[]) : void;
  sendMessage(level: string, message: string) : void;
  sendReset() : void;
  sendStateViewUrl(stateUrl: string) : void;
  sendComputingStatus(status: thmProto.ComputingStatus, computeTimeMS: number) : void;
}

interface BufferedFeedback {
  stateId: number,
  status: coqProto.SentenceStatus,
  worker: string
}

enum InteractionLoopStatus {Idle, CoqCommand, TextEdit};


// 'sticky' flag is not yet supported :()
const lineEndingRE = /[^\r\n]*(\r\n|\r|\n)?/;

export class CoqDocument implements ITextDocument {
  // ITextDocument
  public uri: string;
  public languageId: string = 'coq';
  public getText() {
    return this.documentText;
  }
  public lineCount: number;



  private coqTop: CoqTop;
  private clientConsole: RemoteConsole;
  // private document: ITextDocument;
  private sentences : Sentences = new Sentences();
  private bufferedFeedback: BufferedFeedback[] = [];
  private callbacks : DocumentCallbacks;
  private diagnostics : Diagnostic[] = [];
  private documentText: string;
  private processingLock = new Mutex();
  private resettingLock = new Mutex();
  private cancelProcessing = new CancellationSignal();

  private interactionCommands = new AsyncWorkQueue();
  private interactionLoopStatus = InteractionLoopStatus.Idle;

  constructor(coqtopSettings : thmProto.CoqTopSettings, uri: string, text: string, clientConsole: RemoteConsole, callbacks: DocumentCallbacks) {
    this.clientConsole = clientConsole;
    this.coqTop = new CoqTop(coqtopSettings, clientConsole, {
      onStateStatusUpdate: (x1,x2,x3,x4) => this.onCoqStateStatusUpdate(x1,x2,x3,x4),
      onStateError: (x1,x2,x3,x4) => this.onCoqStateError(x1,x2,x3,x4),
      onEditFeedback: (x1,x2) => this.onCoqEditFeedback(x1,x2),
      onMessage: (x1,x2) => this.onCoqMessage(x1,x2),
      onStateWorkerStatusUpdate: (x1,x2,x3) => this.onCoqStateWorkerStatusUpdate(x1,x2,x3),
      onStateFileDependencies: (x1,x2,x3) => this.onCoqStateFileDependencies(x1,x2,x3),
      onStateFileLoaded: (x1,x2,x3) => this.onCoqStateFileLoaded(x1,x2,x3),
      onClosed: (error?: string) => this.onCoqClosed(error),
    });
    this.documentText = text;
    this.uri = uri;
    this.callbacks = callbacks;
    
    // this.reset();
    
    // Start a worker to handle incomming commands and text edits in a sequential manner
    this.interactionLoop();
  }


  private applyEdit(begin: number, change: TextDocumentContentChangeEvent) : void {
    this.documentText =
      this.documentText.substring(0,begin)
      + change.text
      + this.documentText.substring(begin+change.rangeLength);
  }
  
  /**
   * We can edit if:
   * 1. NOT inside a string or spanning a string deliminator
   * 2. inside a comment and the change preserves the comment boundaries
   * 
   * @returns true if the change should not affect the validity of a sentence (i.e. adjusting whitespace or within a comment)
   */
  private isPassiveEdit(sentences: {length:number; affected:Iterable<Sentence>}, change: TextDocumentContentChangeEvent, beginOffset: number, endOffset: number) : boolean {
    if(sentences.length === 0)
      return true;
    else if(sentences.length > 1)
      return false;
    const sentence = sentences.affected[Symbol.iterator]().next().value;
    return coqParser.isPassiveEdit(this.documentText.substring(sentence.textBegin,sentence.textEnd), beginOffset-sentence.textBegin, endOffset-sentence.textBegin, change.text);
  }

  private async applyTextEdits(changes: TextDocumentContentChangeEvent[]) {
    for(const change of changes) {
      // this.clientConsole.log(`Change: ${rangeToString(change.range)} (${change.rangeLength}) --> ${change.text}`);
      // Remove diagnostics for any text that has been modified
      this.removeDiagnosticsIntersecting(change.range, false);
      // Find offsets for change-range
      const beginOffset = this.offsetAt(change.range.start);
      const endOffset = beginOffset + change.rangeLength;
      // Have any sentences been edited?
      const rangeSent = this.sentences.getRangeAffected(beginOffset,endOffset);
      try {
        if(this.isPassiveEdit(rangeSent,change, beginOffset, endOffset)) {
          // The change won't affect the validity of a sentence, so don't backtrack
        } else if(rangeSent.length > 0) {
          // If sentences have been edited, we need to editAt the END of the change-range
          // and then backtrack to the start of the change-range in order to undo any
          // sentences that have been affected
          await this.cancelCoqOperations();
          let result = await this.editAt(Math.max(endOffset-1,0));
          while(this.sentences.getTip().textBegin > beginOffset)
            await this.stepBackward();
        }
      } catch(err) {
        this.clientConsole.error("Unexpected command failure while applying edits");
        // But in the end, we still have to apply the edits in order to maintain some
        // kind of consistency, so continue working...
      }

      // NOTE: we have to 'await' the above operations to make sure everything has synchronized
      // before commiting changes to the text
      this.applyEdit(beginOffset, change);
      
      // Adjust sentences to reflect space changes
      this.sentences.shiftCharacters(beginOffset, change.text.length - change.rangeLength);
      // And also adjust the diagnostic locations
      this.shiftDiagnostics(textUtil.toRangeDelta(change.range, change.text));
    }

    this.callbacks.sendDiagnostics(this.diagnostics);
      

//       } else if (rangeSent.length == 0) {
//         // Modification between sentences
//         this.applyEdit(begin,change);        
//         this.sentences.shiftCharacters(begin,change.rangeLength);
//         continue;
//       } 
//       
//       // Only one sentence to deal with
//       const editedSentence = rangeSent.affected.next().value;
// 
//       const oldText = this.documentText.substr(begin,change.rangeLength);
//       if(/^\s*$/.test(change.text) && /^\s*$/.test(oldText)
//         && (begin==0 || end==this.documentText.length || /^\s/.test(this.documentText[begin-1]) || /^\s/.test(this.documentText[end]))) {
//         // Allow whitespaces to be adjusted so long as
//         //   1) it occurs within AT MOST one sentence
//         //   2) it does not break or combine a word
//         //   3) it does NOT appear in a quote
//         this.sentences.shiftCharacters(begin,change.rangeLength-oldText.length);
//         this.applyEdit(begin,change);
//       } else if(false) {
//         // Allow text within a comment to be changed as long at the comment deliminators are not changed
//       } else {
//         this.applyEdit(begin,change);
//         this.editAt(begin);
//         continue;
//       }
  }
  
  
  public offsetAt(pos: Position) : number {
    return textUtil.locationAt(this.documentText,pos);
  }

  /**
   * @returns the Position (line, column) for the location (character position)
   */
  public positionAt(offset: number) : Position {
    return textUtil.positionAt(this.documentText, offset);
  }

  // setCoqBinPath(coqBinPath: string) {
  //   this.coqTop.setCoqBinPath(coqBinPath);
  //   this.doResetCoq();
  // }
  
  private sentenceStatusToHighlightType(status: coqProto.SentenceStatus) : thmProto.HighlightType {
    switch(status) {
      case coqProto.SentenceStatus.Complete:
        return thmProto.HighlightType.Complete;
      case coqProto.SentenceStatus.Incomplete:
        return thmProto.HighlightType.Incomplete;
      case coqProto.SentenceStatus.InProgress:
        return thmProto.HighlightType.InProgress;
      case coqProto.SentenceStatus.Parsed:
        return thmProto.HighlightType.Parsing;
      case coqProto.SentenceStatus.Processed:
        return thmProto.HighlightType.Processed;
      case coqProto.SentenceStatus.ProcessingInput:
        return thmProto.HighlightType.Processing;
    }    
  }

  private highlightTypeToSentenceStatus(type: thmProto.HighlightType) : coqProto.SentenceStatus {
    switch(type) {
      case thmProto.HighlightType.Complete:
        return coqProto.SentenceStatus.Complete;
      case thmProto.HighlightType.Incomplete:
        return coqProto.SentenceStatus.Incomplete;
      case thmProto.HighlightType.InProgress:
        return coqProto.SentenceStatus.InProgress;
      case thmProto.HighlightType.Parsing:
        return coqProto.SentenceStatus.Parsed;
      case thmProto.HighlightType.Processed:
        return coqProto.SentenceStatus.Processed;
      case thmProto.HighlightType.Processing:
        return coqProto.SentenceStatus.ProcessingInput;
    }    
  }
  
  private highlightSentence(sentence: Sentence, type?: thmProto.HighlightType) : thmProto.Highlight {
    if(type===undefined)
        type = this.sentenceStatusToHighlightType(sentence.status);
    return {
      style: type,
      textBegin: sentence.textBegin,
      textEnd: sentence.textEnd
    };
  }

  private updateSentenceStatus(sentence: Sentence, status: coqProto.SentenceStatus) : thmProto.Highlight {
    if(sentence.status > status)
      return;
    else {
      if(sentence.computeStart && sentence.status < status) {
        sentence.status = status;

        const duration = process.hrtime(sentence.computeStart);
        sentence.computeTimeMS = duration[0] * 1000.0 + (duration[1] / 1000000.0);

        if(status == coqProto.SentenceStatus.Processed)
          this.clientConsole.log(`processed in time ${sentence.stateId}: ${sentence.computeTimeMS/1000.0} sec`);
      }
      
      sentence.status = status;
      this.callbacks.sendHighlightUpdates([this.highlightSentence(sentence)]);
    }
  }
    
  private applyFeedback(sentence:Sentence, feedback: BufferedFeedback) {
    if(sentence.stateId === feedback.stateId) {
      this.updateSentenceStatus(sentence, feedback.status);
    }
  }
  
  private applyBufferedFeedback(sentence:Sentence) {
    // Process any feedback that we may have seen out of order
    this.bufferedFeedback
      .forEach((feedback,i,a) => this.applyFeedback(sentence, feedback));
    this.bufferedFeedback = [];
  }

  private onCoqStateStatusUpdate(stateId: number, route: number, status: coqProto.SentenceStatus, worker: string) {
    const sent = this.sentences.get(stateId);
    if(sent)
      this.updateSentenceStatus(sent, status);
    else {
      // Sometimes, feedback will be received before CoqTop has given us the new stateId,
      // So we will buffer these messages until we get the next 'value' response.
      this.bufferedFeedback.push({stateId: stateId, status: status, worker: worker});
    }
  }
  
  private onCoqStateError(stateId: number, route: number, message: string, location?: coqProto.Location) {
    const sent = this.sentences.get(stateId);
    if(sent) {
      let errorBegin: number, errorEnd : number;
      if(location) {
         errorBegin = sent.textBegin + location.start;
         errorEnd = sent.textBegin + location.stop;
      } else {
         errorBegin = sent.textBegin;
         errorEnd = sent.textEnd;        
      }
      
      this.callbacks.sendHighlightUpdates([
        this.highlightSentence(sent, thmProto.HighlightType.TacticFailure)
        ]);

      this.addDiagnostic({
        message: message,
        range: Range.create(this.positionAt(errorBegin), this.positionAt(errorEnd)),
        severity: DiagnosticSeverity.Error
        });
    }
  }
  
  
  private onCoqEditFeedback(editId: number, error?: coqProto.ErrorMessage) {
    // if(feedback.error) {
    //   const errorBegin = feedback.error.
    //   this.addDiagnostic({
    //     message: feedback.error.message,
    //     range: Range.create(this.positionAt(errorBegin), this.positionAt(errorEnd)),
    //     severity: DiagnosticSeverity.Error
    //     });
    // }
  }
  
  private onCoqMessage(level: coqProto.MessageLevel, message: string) {
    this.callbacks.sendMessage(coqProto.MessageLevel[level], message);
  }

  private onCoqStateWorkerStatusUpdate(stateId: number, route: number, workerUpdates: coqProto.WorkerStatus[]) {
  }

  private onCoqStateFileDependencies(stateId: number, route: number, fileDependencies: Map<string,string[]>) {
  }

  private onCoqStateFileLoaded(stateId: number, route: number, status: coqProto.FileLoaded) {
  }
  
  private async onCoqClosed(error?: string) {
    if(!error)
      return;
    this.clientConsole.log(`onCoqClosed(${error})`);
    try {
      await this.cancelCoqOperations();
    } finally {
      this.callbacks.sendReset();
      this.clientConsole.log('completed onCoqClosed()');
    }
  }
  
  
  private async doResetCoq() {
    this.clientConsole.log('doResetCoq()');
    try {
      this.clientConsole.log('resetting coqtop');
      let value = await this.coqTop.resetCoq();
      this.sentences.reset(value.stateId);
    } finally {
      this.callbacks.sendReset();
      this.clientConsole.log('completed doResetCoq()');
    }
  }

  
  private async cancellableOperation<T>(operation: Thenable<T>) : Promise<T> {
    return await Promise.race<T>(
      [ operation
      , this.cancelProcessing.event.then(() => Promise.reject<T>('operation cancelled'))
      ]);
  }

  /**
   * @param currentSentence: where to start parsing the next sentence
   * @param maxOffset: do not parse past maxOffset
   * @returns the next parsed sentence OR else null if parsing exceeds @maxOffset
   */
  private async plainStepForward(currentSentence: Sentence, maxOffset?: number) : Promise<{value: coqProto.CoqValue, nextSentence?: Sentence, isUnfocused: boolean}> {

    let startPos = currentSentence.textEnd;
    let docText = this.documentText;
    const sentenceLength = coqParser.parseSentence(this.documentText.substr(startPos));
    if(sentenceLength == -1)
      return null;
    let stopPos = startPos + sentenceLength;
    
    if(maxOffset!==undefined && stopPos > maxOffset)
      return null;
    
    let command = docText.substring(startPos, stopPos);

    // Preliminary "parsing" highlight
    const parsingHighlights = [
      { style: thmProto.HighlightType.Parsing, textBegin: startPos, textEnd: stopPos }
      ];
    this.callbacks.sendHighlightUpdates(parsingHighlights);

    // ????
    // This might either be the textual starting location of the command we're submitting
    // or else an edit-state identifier to keep stuff in sync. 
    const editId = -currentSentence.stateId;

    const startTime = process.hrtime();
    try {
      const value = await this.coqTop.coqAddCommand(command, editId, currentSentence.stateId);

      const nextSentence = this.sentences.addChild(currentSentence,value.stateId,startPos,stopPos);
      nextSentence.computeStart = startTime;
      this.applyBufferedFeedback(nextSentence);
      this.updateSentenceStatus(nextSentence,coqProto.SentenceStatus.ProcessingInput);

      if(value.unfocusedStateId) {
        this.sentences.setTip(value.unfocusedStateId);
        return {value:value, nextSentence: this.sentences.get(value.unfocusedStateId), isUnfocused: true};
      } else
        return {value:value, nextSentence: nextSentence, isUnfocused: false};
    } catch(err) {
      const error = <FailureResult>err;

      const errorBegin = startPos + error.range.start;
      const errorEnd = startPos + error.range.stop;

      const highlights = [
        { style: thmProto.HighlightType.Clear, textBegin: startPos, textEnd: stopPos }
        // { style: thmProto.HighlightType.SyntaxError, textBegin: errorEnd, textEnd: errorEnd },
        ];
      this.callbacks.sendHighlightUpdates(highlights);

      this.addDiagnostic({
        message: error.message,
        range: Range.create(this.positionAt(errorBegin), this.positionAt(errorEnd)),
        severity: DiagnosticSeverity.Error
        });

      throw error;      
    }
  }

  private addDiagnostic(diagnostic: Diagnostic) {
    this.diagnostics.push(diagnostic);
    this.callbacks.sendDiagnostics(this.diagnostics);
  }

  private removeDiagnosticsContaining(pos: Position, sendUpdate?: boolean) {
    this.diagnostics = this.diagnostics
      .filter((d) => !textUtil.rangeContains(d.range, pos));
    if(sendUpdate === undefined || sendUpdate===true)
      this.callbacks.sendDiagnostics(this.diagnostics);
  }

  private removeDiagnosticsIntersecting(range: Range, sendUpdate?: boolean) {
    this.diagnostics = this.diagnostics
      .filter((d) => !textUtil.rangeTouches(d.range, range));
    if(sendUpdate === undefined || sendUpdate===true)
      this.callbacks.sendDiagnostics(this.diagnostics);
  }
  

  private shiftDiagnostics(delta: textUtil.RangeDelta) {
    for(let idx = 0; idx < this.diagnostics.length; ++idx) {
      this.diagnostics[idx].range = textUtil.rangeTranslate(this.diagnostics[idx].range, delta);
    }
  }
  
  private convertGoal(goal: coqProto.Goal) : thmProto.Goal {
    return <thmProto.Goal>{
      goal: goal.goal,
      hypotheses: goal.hypotheses.map((hyp) => {
        var h = hyp.split(/(:=|:)([^]*)/);
        return {identifier: h[0].trim(), relation: h[1].trim(), expression: h[2].trim()};
      })
    };
  }
  
  private convertGoals(goals: GoalResult) : thmProto.CoqTopGoalResult {
    return {
      goals: goals.goals ? goals.goals.map(this.convertGoal) : undefined,
      backgroundGoals: goals.backgroundGoals ? goals.backgroundGoals.map(this.convertGoal) : undefined,
      shelvedGoals: goals.shelvedGoals ? goals.shelvedGoals.map(this.convertGoal) : undefined,
      abandonedGoals: goals.abandonedGoals ? goals.abandonedGoals.map(this.convertGoal) : undefined,
      };
      
  }

  /**
   * 
   *  */  
  private async rawGetGoal(stateId?: number) : Promise<thmProto.CoqTopGoalResult> {
    var result = this.convertGoals(await this.coqTop.coqGoal());
    if(stateId !== undefined)
      this.sentences.setGoalState(stateId, result);
    return result;
  }

  private async getGoal(stateId?: number) : Promise<thmProto.CoqTopGoalResult> {
    try {
      return await this.rawGetGoal(stateId);
    } catch(err) {
      const error = <FailureResult>err;
      const e = <coqProto.FailValue>{
        message: error.message,
        location: error.range
        };
      return {error: e};
    }
  }

  
  private clearSentenceHighlight(sentence: Sentence, endSentence?: Sentence) {
    this.callbacks.sendHighlightUpdates([{
      style: thmProto.HighlightType.Clear,
      textBegin: sentence.textBegin,
      textEnd: endSentence ? endSentence.textEnd : sentence.textEnd
    }]);
  }

  private clearSentenceHighlightAfter(sentence: Sentence, endSentence?: Sentence) {
    this.callbacks.sendHighlightUpdates([{
      style: thmProto.HighlightType.Clear,
      textBegin: sentence.textEnd,
      textEnd: endSentence ? endSentence.textEnd : sentence.textEnd
    }]);
  }

  /**
   * 
   *  */  
  private async stepForwardUntil(maxOffset?: number, stopWhenUnfocused?: boolean) : Promise<Sentence> {
    if(!this.coqTop.isRunning())
      throw "Coq has not been initialized";

    stopWhenUnfocused = (stopWhenUnfocused==undefined) ? false : stopWhenUnfocused;
    
    // grab the head sentences
    // TODO: support other edit points 
    let currentSentence = this.sentences.getTip();

    // this.clientConsole.log("Step To End");

    try {
      while(true) {
        const interp = await this.plainStepForward(currentSentence,maxOffset);

        if(!interp)
          return null;
        else if(stopWhenUnfocused && interp.isUnfocused)
          return interp.nextSentence;
        currentSentence = interp.nextSentence;
      }
    } catch(err) {
      const error = <FailureResult>err;
      
      if(error.stateId) {
        const beforeErrorSentence = this.sentences.get(error.stateId);
        this.rollbackState(beforeErrorSentence,currentSentence);
      }
      
      throw error;
    }
  }
  
  private async jumpToLocation(sentence : Sentence) {
    try {
      const editResult = await this.coqTop.coqEditAt(sentence.stateId);
      if(editResult.newFocus) {
        // Jumping inside another proof; create a new tip
        const qedSentence = this.sentences.get(editResult.newFocus.qedStateId);
        this.sentences.rewindToWithLast(sentence,qedSentence);
        this.clearSentenceHighlightAfter(sentence,qedSentence);
      } else if(sentence.textEnd <= this.sentences.getTip().textBegin) {
        // Simple rewind
        this.clearSentenceHighlightAfter(sentence,this.sentences.getTip());
        this.sentences.rewindTo(sentence);
      } else {
        // not sure what to make of this state
        const a = 5;
  //      throw "Jumping to a new state; not sure what to do in this situation...?";
      }
    } catch(err) {
      const error = <FailureResult>err;
      const beforeErrorSentence = this.sentences.get(error.stateId);
      await this.coqTop.coqEditAt(error.stateId);

      this.clearSentenceHighlightAfter(beforeErrorSentence,sentence);
      this.sentences.rewindTo(beforeErrorSentence);
    }
  }
  
  private async editAt(location: number) : Promise<thmProto.CoqTopGoalResult> {
    const currentSentence = this.sentences.getTip();

    try {
      if(location >= currentSentence.textEnd) {
        // We need to step forward to reach the location.
        // We might be focused in the middle of a proof, so even if there is a
        // closer state we can jump to, we cannot call coqEditAt just yet.
        // (Or else we will get a Coq anomally :/ )
        const forwardSentence = await this.stepForwardUntil(location, true /* stop if we become unfocused */);
        if(forwardSentence === null) {
          return await this.rawGetGoal();          
        }
        // At this point, either we have reached the location we're looking for,
        // or else the proof has become unfocused (the current state might be
        // anywhere) and we will need to call coqEditAt to get closer to the location.      
        const closestSentence = this.sentences.findPrecedingSentence(location);
        // Are we at the closest sentence?
        if(forwardSentence.stateId !== closestSentence.stateId) {
          // No; jump there
          await this.jumpToLocation(closestSentence);
        }
        // We can now step forward directly to the location
        return await this.interpretToEnd(location);
      } else {
        // Our desired location is above us; we'll have to jump there
        const closestSentence = this.sentences.findPrecedingSentence(location);
        await this.jumpToLocation(closestSentence);
        return await this.rawGetGoal();
      }
    } catch(error) {
      return this.errorGoalResult(error);
    }
  }


  private errorGoalResult(error: FailureResult) : thmProto.CoqTopGoalResult {
    const e = <coqProto.FailValue>{
      message: error.message,
      location: error.range
      };
    return {error: e};
  }

  /**
   * 
   *  */  
  private async interpretToEnd(maxOffset?: number) : Promise<thmProto.CoqTopGoalResult> {
    let currentSentence = this.sentences.getTip();
    
    try {
      await this.stepForwardUntil(maxOffset);
      
      return await this.rawGetGoal();
    } catch(error) {
      return this.errorGoalResult(error);
    }
  }

  private async rollbackState(startingSentence: Sentence, endSentence?: Sentence) {
    if(this.sentences.getTip().stateId !== startingSentence.stateId) {
      // Undo the sentence
this.clientConsole.log("rolling back state");
      await this.coqTop.coqEditAt(startingSentence.stateId);
      this.sentences.rewindTo(startingSentence);
      if(endSentence !== undefined)
        this.clearSentenceHighlightAfter(startingSentence,endSentence);
this.clientConsole.log("rolled back");
    }
  }
  
  
  private async stepForward() : Promise<thmProto.CoqTopGoalResult> {
    const currentSentence = this.sentences.getTip();
    try {
      const interp = await this.plainStepForward(currentSentence);
      if(!interp)
        return {}

      return await this.rawGetGoal(interp.nextSentence ? interp.nextSentence.stateId : undefined);
    } catch(error) {
      this.rollbackState(currentSentence);
      return this.errorGoalResult(error);
    }
  }
  
  /**
   * 
   *  */  
  private async stepBackward() : Promise<thmProto.CoqTopGoalResult> {
    // grab the tip sentence
    const currentSentence = this.sentences.getTip();

    try {
      const prevSentence = this.sentences.getPredecessor(currentSentence);

      if(prevSentence == null) {
        await this.doResetCoq();
        return {};
      }

      await this.coqTop.coqEditAt(prevSentence.stateId);
      this.sentences.rewindTo(prevSentence);
      this.callbacks.sendHighlightUpdates([
        this.highlightSentence(currentSentence, thmProto.HighlightType.Clear)
        ]);
      return await this.rawGetGoal(prevSentence.stateId);
    } catch(err) {
      const error = <FailureResult>err;
      const beforeErrorSentence = this.sentences.get(error.stateId);
      await this.coqTop.coqEditAt(error.stateId);

      this.clearSentenceHighlightAfter(beforeErrorSentence,currentSentence);
      this.sentences.rewindTo(beforeErrorSentence);
      return await this.getGoal();
    }

  }
  
  public async close() {
    return await this.coq.quit();
  }

  private async protectOperation(op: (wasReset:boolean)=>Promise<thmProto.CoqTopGoalResult>, lazyInitialize?: boolean) : Promise<thmProto.CoqTopGoalResult> {
    lazyInitialize = (lazyInitialize===undefined) ? true : false;
    let unlock : () => Promise<void>; 
    try {
      unlock = await this.processingLock.lock(this.cancelProcessing.event);
    } catch(reason) {
      return <coqProto.FailValue>{message: "operation cancelled"};
    }
    try {
      if(!this.coqTop.isRunning()) {
        if(!lazyInitialize)
          return {};
        await this.cancellableOperation(this.doResetCoq());
        const result = await this.cancellableOperation(op(true));
      } else
        return await this.cancellableOperation(op(false));
    } catch(reason) {
      return <coqProto.FailValue>{message: reason};
    } finally {
      unlock();
    }
  }  
  
  private interrupt() {
    this.coqTop.coqInterrupt();
  }


  /**
   * This loop handles each coq command and text edit sequentially.
   * One of the requirements is that a command's document position is still valid when it returns so that we can report accurate error messages, so text edits that arrive while a command is being processed are delayed until the command finished so that we do not invalidate its document positions.
   * 
   * To cancel the current queue of commands, call cancelCoqOperations()  
   */
  private async interactionLoop() {
    while(true) {
      try {
        await this.interactionCommands.executeOneTask();
      } catch(error) {
        this.clientConsole.warn(`Interaction loop exception: ${error}`);
      } finally {
      }
    }
  }
  
  /**
   * Ensures that the text edits are applied *after* the currently scheduled operations; this delay prevents their document positions from being invalidated too soon 
   */
  public textEdit(changes: TextDocumentContentChangeEvent[]) {
    return this.interactionCommands.process<void>(async () => {
      this.interactionLoopStatus = InteractionLoopStatus.TextEdit;
      try {
        return await this.applyTextEdits(changes);
      } finally {
        this.interactionLoopStatus = InteractionLoopStatus.Idle;
      }
    });
  }


  private updateComputingStatus(status, startTime: number[]) {
    const duration = process.hrtime(startTime);
    const interval = duration[0] * 1000.0 + (duration[1] / 1000000.0);
    this.callbacks.sendComputingStatus(status, interval);
  }

  private async doCoqOperation<X>(task: ()=>Promise<X>, lazyInitializeCoq? : boolean) {
    lazyInitializeCoq = (lazyInitializeCoq===undefined) ? true : lazyInitializeCoq;
    if(!this.coqTop.isRunning()) {
      if(lazyInitializeCoq) {
        await this.doResetCoq();
      } else
        return {};
    }
    
    return await task();
  }

  private enqueueCoqOperation<X>(task: ()=>Promise<X>, lazyInitializeCoq? : boolean) {
    // this.cancelProcessing might change in the future, so we want to make sure that, when
    // the task is eventually run, it will use the CURRENT this.cancelProcessing
    const cancelSignal = this.cancelProcessing;
    return this.interactionCommands.process<X>(async () => {
      if(cancelSignal.isCancelled())
        return Promise.reject<X>(<coqProto.FailValue>{message: 'operation cancelled'})
        
      this.interactionLoopStatus = InteractionLoopStatus.CoqCommand;
      const startTime = process.hrtime();
      const statusCheck = setInterval(() => this.updateComputingStatus(thmProto.ComputingStatus.Computing, startTime), 500);
      var interrupted = false;
      try {
        return await Promise.race<X>(
          [ this.doCoqOperation(task, lazyInitializeCoq)
          , cancelSignal.event.then(() => Promise.reject<X>(<coqProto.FailValue>{message: 'operation cancelled'}))
          ]);
      } catch(error) {
        this.updateComputingStatus(thmProto.ComputingStatus.Interrupted, startTime);
        interrupted = true;
        throw error;
      } finally {
        this.interactionLoopStatus = InteractionLoopStatus.Idle;
        clearInterval(statusCheck);
        if(!interrupted)
          this.updateComputingStatus(thmProto.ComputingStatus.Finished, startTime);
      }
    });
  }
  
  /**
   * Cancels all coq commands that are associated with `cancelProcessing`, which should be every coq command in `interactionCommands`.
   * If a text edit invalidates a state, then this method should also be called.
   */
  private cancelCoqOperations() : Promise<void> {
    // Cancel all current and pending operations
    this.cancelProcessing.cancel();
    // Do not cancel subsequent operations
    this.cancelProcessing = new CancellationSignal();
    if(this.interactionLoopStatus === InteractionLoopStatus.CoqCommand)
      return this.coqTop.coqInterrupt();
  }
  
  private async interactionsCoqQuit() {
    const waitMS = 1000;
    const cancelling = this.cancelCoqOperations();
    try {
      await Promise.race<{}>([cancelling, new Promise((resolve,reject) => setTimeout(() => reject(), waitMS))]);
    } finally {
      await this.coqTop.coqQuit();
    }
  }
  
  private async interactionsCoqReset() {
    const waitMS = 1000;
    const cancelling = this.cancelCoqOperations();
    try {
      await Promise.race<{}>([cancelling, new Promise((resolve,reject) => setTimeout(() => reject(), waitMS))]);
    } finally {
      await this.doResetCoq();
    }
  }

  private coqInterface = {
      stepForward: () => this.enqueueCoqOperation(async () => await this.stepForward(), true),
      stepBackward: () => this.enqueueCoqOperation(() => this.stepBackward(), true),
      interpretToPoint: (offset) => this.enqueueCoqOperation(() => this.editAt(offset), true),
      interpretToEnd: () => this.enqueueCoqOperation(() => this.interpretToEnd(), true),
      getGoals: () => this.enqueueCoqOperation(() => this.getGoal(), true),
      locate: (query: string) => this.enqueueCoqOperation(async () => ({searchResults: await this.coqTop.coqQuery("Locate " + query + ".")}), true),
      check: (query: string) => this.enqueueCoqOperation(async () => ({searchResults: await this.coqTop.coqQuery("Check " + query + ".")}), true),
      search: (query: string) => this.enqueueCoqOperation(async () => ({searchResults: await this.coqTop.coqQuery("Search " + query + ".")}), true),
      searchAbout: (query: string) => this.enqueueCoqOperation(async () => ({searchResults: await this.coqTop.coqQuery("SearchAbout " + query + ".")}), true),
      resizeWindow: (columns: number) => this.enqueueCoqOperation(() => this.coqTop.coqResizeWindow(columns), false),
      quit: () => this.interactionsCoqQuit(),
      reset: () => this.interactionsCoqReset(),
      interrupt: () => this.cancelCoqOperations(),
    };
  // private coqInterface = {
  //     stepForward: () => this.protectOperation((wasReset) => this.stepForward()),
  //     stepBackward: () => this.protectOperation((wasReset) => this.stepBackward()),
  //     interpretToPoint: (offset) => this.protectOperation((wasReset) => this.editAt(offset)),
  //     interpretToEnd: () => this.protectOperation((wasReset) => this.interpretToEnd()),
  //     getGoals: () => this.protectOperation(async (wasReset) => this.getGoal()),
  //     quit: () => {this.coqTop.coqQuit(); return {}},
  //     reset: () => this.doResetCoq(),
  //     interrupt: () => {
  //       if(this.processingLock.isLocked())
  //         this.coqTop.coqInterrupt();
  //     },
  //     locate: (query: string) => this.protectOperation((wasReset) => this.coqTop.coqQuery("Locate " + query + ".")),
  //     check: (query: string) => this.protectOperation((wasReset) => this.coqTop.coqQuery("Check " + query + ".")),
  //     search: (query: string) => this.protectOperation((wasReset) => this.coqTop.coqQuery("Search " + query + ".")),
  //     searchAbout: (query: string) => this.protectOperation((wasReset) => this.coqTop.coqQuery("SearchAbout " + query + ".")),
  //     resizeWindow: (columns: number) => this.coqTop.coqResizeWindow(columns),
  //   };
  
  public get coq() {
    return this.coqInterface; 
  }
}


