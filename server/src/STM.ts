'use strict'

import {Position, Range, TextDocumentContentChangeEvent, TextDocument, RemoteConsole} from 'vscode-languageserver';
import {CancellationToken} from 'vscode-jsonrpc';
import * as vscode from 'vscode-languageserver';
import * as coqProto from './coq-proto';
import * as util from 'util';
import * as proto from './protocol';
import * as textUtil from './text-util';
import * as coqtop from './coqtop';
import {ProofView, Goal, Hypothesis, HypothesisDifference, TextDifference, TextPartDifference} from './protocol';
import * as coqParser from './coq-parser';
import {Sentence, SentenceError} from './STMSentence';
type StateId = number;

interface BufferedFeedback {
  stateId: number,
  status: coqProto.SentenceStatus,
  worker: string
}

export interface StateMachineCallbacks {
  sentenceStatusUpdate(range: Range, status: coqProto.SentenceStatus) : void;
  clearSentence(range: Range) : void;
  updateStmFocus(focus: Position): void;
  error(sentenceRange: Range, errorRange: Range, message: string, rich_message?: any) : void;
  message(level: coqProto.MessageLevel, message: string, rich_message?: any) : void;
  ltacProfResults(range: Range, results: coqProto.LtacProfResults) : void;
  coqDied(error?: string) : void;
}

export type CommandIterator = (begin: Position, end?: Position) => Iterable<{text: string, range: Range}>;

export type GoalErrorResult = proto.NotRunningResult | proto.FailureResult | proto.InterruptedResult
export type GoalResult = proto.NoProofResult | proto.NotRunningResult |
  proto.FailureResult |
  proto.ProofViewResult |
  proto.InterruptedResult

class InconsistentState {
  constructor(
    public message: string
  ) {}
}

class AddCommandFailure implements proto.FailValue {
  constructor(
    public message: string,
    public range: vscode.Range,
    public sentence: vscode.Range)
  {} 
}

/**
 * Manages the parts of the proof script that have been interpreted and processed by coqtop
 * 
 * Abstractions:
 * - addCommands(range: Range, commandText: string)
 *    ensures that the as much of commandText has been processed; cancels any previously overlapping sentences as needed
 *    returns the actual range that was accepted
 * - serialization: Coq commands may only run one at a time but are asynchronous. This STM ensures that each command is run one at a time, that edits are applied only when the prior commands are run
 * - interruption: queued may be interrupted; clears the queue of commands, interrupts coq, and applies the queued edits 
 */
export class CoqStateMachine {
  private version = 0;
  // lazy init
  private root : Sentence = null;
  // map id to sentence; lazy init  
  private sentences : Map<StateId,Sentence> = null;
  // The sentence that coqtop considers "focused"; lazy init
  private focusedSentence : Sentence = null;
  // The sentence that is closest to the end of the document; lazy init
  private lastSentence : Sentence = null;
  // Handles communication with coqtop
  private coqtop : coqtop.CoqTop;
  // feedback may arrive before a sentence is assigned a stateId; buffer feedback messages for later
  private bufferedFeedback: BufferedFeedback[] = [];
  private documentVersion: number;
  private running = true;
  // When it is not prudent to interrupt Coq, e.g. cancelling a sentence:
  private disableInterrupt = false;
  /** The error from the most recent Coq command (`null` if none) */
  private currentError : proto.FailValue = null; 

  constructor(private settings: proto.CoqTopSettings
    , private callbacks: StateMachineCallbacks
    , private console: RemoteConsole
  ) {
    this.coqtop = new coqtop.CoqTop(settings, console, {
      onStateStatusUpdate: (x1,x2,x3,x4) => this.onCoqStateStatusUpdate(x1,x2,x3,x4),
      onStateError: (x1,x2,x3,x4) => this.onCoqStateError(x1,x2,x3,x4),
      onEditFeedback: (x1,x2) => this.onCoqEditFeedback(x1,x2),
      onMessage: (x1,x2,x3) => this.onCoqMessage(x1,x2,x3),
      onStateWorkerStatusUpdate: (x1,x2,x3) => this.onCoqStateWorkerStatusUpdate(x1,x2,x3),
      onStateFileDependencies: (x1,x2,x3) => this.onCoqStateFileDependencies(x1,x2,x3),
      onStateFileLoaded: (x1,x2,x3) => this.onCoqStateFileLoaded(x1,x2,x3),
      onStateLtacProf: (x1,x2,x3) => this.onCoqStateLtacProf(x1,x2,x3),
      onClosed: (error?: string) => this.onCoqClosed(error),
    });
  }

  public dispose() {
    if(this.running)
      this.console.warn("The STM manager is being disposed before being shut down");
    this.running = false;
    this.sentences = undefined;
    this.bufferedFeedback = undefined;
    this.console = undefined;
    this.setFocusedSentence(undefined);
    this.callbacks = undefined;
    if(this.coqtop)
      this.coqtop.dispose();
  }

  public async shutdown() {
    if(!this.running)
      return;
    await this.coqtop.coqQuit();
    this.dispose();
  }

  public async interrupt() : Promise<void> {
    try {
      await this.coqtop.coqInterrupt();
    } catch(err) {
      // this will fail on user interrupt
      this.console.error('Exception thrown while interrupting Coq: ' + err.toString());
    }
  }

  public isRunning() {
    return this.running;
  }


  /**
   * @returns the document position that Coqtop considers "focused"; use this to update the cursor position or
   * to determine which commands to add when stepping through a script.
   */
  public getFocusedPosition() : Position {
    if(!this.focusedSentence)
      return Position.create(0,0);
    return this.focusedSentence.getRange().end;
  }

  /**
   * Adds the next command
   * @param verbose - generate feedback messages with more info
   * @throw proto.FailValue if advancing failed
   */
  public async stepForward(commandSequence: CommandIterator, verbose: boolean = false) : Promise<(proto.FailureResult & proto.FocusPosition)|null>  {
    await this.validateState(true);
    const currentFocus = this.getFocusedPosition();
    try {
    // Advance one statement: the one that starts at the current focus
    await this.iterateAdvanceFocus(
      { iterateCondition: (command,contiguousFocus) => textUtil.positionIsEqual(command.range.start, currentFocus)
      , commandSequence: commandSequence
      , verbose: verbose
      });
    } catch (error) {
      if(error instanceof AddCommandFailure)
        return Object.assign(Object.assign(error, <proto.FailureTag>{type: 'failure'}), <proto.FocusPosition>{focus: this.getFocusedPosition()});
      else
        throw error;
    }
  }

  /**
   * Steps back from the currently focused sentence
   * @param verbose - generate feedback messages with more info
   * @throw proto.FailValue if advancing failed
   */
  public async stepBackward() : Promise<void>  {
    await this.validateState(true);
    await this.cancelSentence(this.focusedSentence);
  }


  /** Adjust sentence ranges and cancel any sentences that are invalidated by the edit
   * @param isInvalidated: a function to determine whether an intersecting change is passive (i.e. changes the meaning of a sentence); returns true if the change invalidates the sentence.
  */
  public async applyChanges(changes: TextDocumentContentChangeEvent[], newVersion: number) {
    if(!this.running || changes.length == 0)
      return;

    // sort the edits such that later edits are processed first
    // this way, we do not have to adjust the change position as we modify the document
    // vscode guarantees that no changes overlap
    let sortedChanges =
      changes.sort((change1, change2) =>
        textUtil.positionIsAfter(change1.range.start, change2.range.start) ? -1 : 1)

    // this.console.log(`Sentences before:`);
    // this.logDebuggingSentences(this.debuggingGetSentences())

    try {
      const cancellations : Promise<void>[] = [];

      const deltas = sortedChanges.map((c) => textUtil.toRangeDelta(c.range,c.text))

      for (let sent of this.lastSentence.backwards()) {
        // // optimization: remove any changes that will no longer overlap with the ancestor sentences
        // while (sortedChanges.length > 0 && textUtil.positionIsAfterOrEqual(sortedChanges[0].range.start, sent.getRange().end)) {
        //   // this change comes after this sentence and all of its ancestors, so get rid of it
        //   sortedChanges.shift();
        // }
        // // If there are no more changes, then we are done adjusting sentences
        // if (sortedChanges.length == 0)
        //   break sent; // sent

        // apply the changes
        const preserved = sent.applyTextChanges(sortedChanges,deltas);
        if(!preserved) {
// this.console.log("cancelling: " + createDebuggingSentence(sent));
          cancellations.push(this.cancelSentence(sent));
        }

      } // for sent in ancestors of last sentence

      await this.noInterrupt(() => Promise.all(cancellations));
    } catch(err) {
      this.handleInconsistentState(err);
    }
    // this.console.log("Sentences After:");
    // this.logDebuggingSentences(this.debuggingGetSentences())

    this.version = newVersion;
  }

  private convertCoqTopError(err) : GoalErrorResult {
    if(err instanceof coqtop.Interrupted)
      return {type: 'interrupted', range: this.sentences.get(err.stateId).getRange()}
    else if(err instanceof coqtop.CoqtopError)
      return {type: 'not-running', message: err.message}
    // else if(err instanceof coqtop.CallFailure) {
    //   const sent = this.sentences.get(err.stateId);
    //   const start = textUtil.positionAtRelative(sent.getRange().start,sent.getText(),err.range.start);
    //   const end = textUtil.positionAtRelative(sent.getRange().start,sent.getText(),err.range.stop);
    //   const range = Range.create(start,end); // err.range
    //   return Object.assign<proto.FailureTag,proto.FailValue>({type: 'failure'}, <proto.FailValue>{message: err.message, range: range, sentence: this.sentences.get(err.stateId).getRange()})
    else
      throw err;
  }

  /**
   * Return the goal for the currently focused state
   * @throws FailValue
   */
  public async getGoal() : Promise<GoalResult> {
    if(!this.isCoqReady())
      return {type: 'not-running'}
    try {
      const result = await this.coqtop.coqGoal();
      return this.convertGoals(result);
    } catch(error) {
      this.console.log("getGoal error: " + util.inspect(error,false,undefined));
      if(error instanceof coqtop.CallFailure) {
      this.console.log("is coqtop.CallFailure");
        const sent = this.focusedSentence;
        const failure = await this.handleCallFailure(error, {range: sent.getRange(), text: sent.getText() });
        return Object.assign(failure, <proto.FailureTag>{type: 'failure'})
      } else
        return this.convertCoqTopError(error)
    }
  }

  /** Interpret to point
   * Tell Coq to process the proof script up to the given point
   * This may not fully process everything, or it may rewind the state.
   * @throw proto.FailValue if advancing failed
   */
  public async interpretToPoint(position: Position, commandSequence: CommandIterator, token: CancellationToken) : Promise<(proto.FailureResult & proto.FocusPosition)|null> {
    await this.validateState(true);
    try {
      // Advance the focus until we reach or exceed the location
      await this.iterateAdvanceFocus(
        { iterateCondition: (command,contiguousFocus) =>
            textUtil.positionIsAfterOrEqual(position,command.range.end) && !token.isCancellationRequested
        , commandSequence: commandSequence
        , end: position
        , verbose: true
        });
      if(token.isCancellationRequested)
        throw "operation interrupted"

      if(textUtil.positionIsBefore(position,this.getFocusedPosition())) {
        // We exceeded the desired position
        await this.focusSentence(this.getParentSentence(position));
      }
    } catch (error) {
      if(error instanceof AddCommandFailure)
        return Object.assign(Object.assign(error, <proto.FailureTag>{type: 'failure'}), <proto.FocusPosition>{focus: this.getFocusedPosition()});
      else
        throw error;
    }
  }

  public async doQuery(query: string, position?: Position) : Promise<string> {
    await this.validateState(true);
    let state: StateId = undefined;
    if(position)
      state = this.getParentSentence(position).getStateId();
    return await this.coqtop.coqQuery(query, state)
  }

  public async setWrappingWidth(columns: number) : Promise<void> {
    if(this.isCoqReady())
      this.coqtop.coqResizeWindow(columns);
  }

  public async requestLtacProfResults(position?: Position) : Promise<void> {
    if(!this.isCoqReady())
      return;
    if(position !== undefined) {
      const sent = this.getSentence(position);
      if(sent) {
        await this.coqtop.coqLtacProfilingResults(sent.getStateId());
        return;
      }
    }
    await this.coqtop.coqLtacProfilingResults();
  }
  //     ltacProfResults: (offset?: number) => this.enqueueCoqOperation(async () => {
  //       if(offset) {
  //         const sent = this.sentences.findAtTextPosition(offset);
  //         return this.coqTop.coqLtacProfilingResults(sent===null ? undefined : sent.stateId);
  //       } else
  //         return this.coqTop.coqLtacProfilingResults();
  //     }, true),
  

  public *getSentences() : Iterable<{range: Range, status: coqProto.SentenceStatus}> {
    if(!this.running)
      return
    for(let sent of this.root.descendants())
      yield { range: sent.getRange(), status: sent.getStatus()}
  }

  public *getSentenceErrors() : Iterable<SentenceError> {
    if(!this.running)
      yield
    for(let sent of this.root.descendants()) {
      if(sent.getError())
        yield sent.getError();
    }
  }

  public *getErrors() : Iterable<SentenceError> {
    if(!this.running)
      return;
    yield *this.getSentenceErrors();
    if(this.currentError !== null)
      yield this.currentError;
  }

  private getParentSentence(position: Position) : Sentence {
    for(let sentence of this.root.descendants()) {
      if(!sentence.isBefore(position))
        return sentence.getParent();
    }
    // This should never be reached
    return this.root;
  }

  private getSentence(position: Position) : Sentence {
    for(let sentence of this.root.descendants()) {
      if(sentence.contains(position))
        return sentence;
    }
    // This should never be reached
    return this.root;
  }

  private initialize(rootStateId: StateId) {
    if(this.root != null)
      throw "STM is already initialized."
    if(!this.running)
      throw "Cannot reinitialize the STM once it has died; create a new one."
    this.root = Sentence.newRoot(rootStateId);
    this.sentences = new Map<StateId,Sentence>([ [this.root.getStateId(),this.root] ]);
    this.lastSentence = this.root;
    this.setFocusedSentence(this.root);
  }

  /** Assert that we are in a "running"" state
   * @param initialize - initialize Coq if true and Coq has not yet been initialized
   * @returns true if it is safe to communicate with coq
  */
  private isCoqReady() : boolean {
    return this.running && this.coqtop.isRunning();
  }

  /** Assert that we are in a "running"" state
   * @param initialize - initialize Coq if true and Coq has not yet been initialized
   * @returns true if it is safe to communicate with coq
  */
  private async validateState(initialize: boolean) : Promise<boolean> {
    if(!this.running && initialize)
      throw "Cannot perform operation: coq STM manager has been shut down."
    else if(!this.running)
      return false;
    else if(this.coqtop.isRunning())
      return true;
    else if(initialize) {
      let value = await this.coqtop.resetCoq();
      this.initialize(value.stateId);
      return true;
    } else
      return false;
  }

  private async noInterrupt<T>(fun: () => Promise<T>) : Promise<T> {
    try {
      this.disableInterrupt = true;
      return await fun()
    } finally {
      this.disableInterrupt = false;
    }
  }

  /** Continues to add next next command until the callback returns false.
   * Commands are always added from the current focus, which may advance seuqentially or jump around the Coq script document
   * 
   * @param params.end: optionally specify and end position to speed up command parsing (for params.commandSequence) 
   * */
  private async iterateAdvanceFocus(params: {iterateCondition: (command: {text:string,range:Range}, contiguousFocus: boolean)=>boolean, commandSequence: CommandIterator, verbose: boolean, end?: Position}) : Promise<void> {
    // true if the focus has not jumped elsewhere in the document
    let contiguousFocus = true;
    // Start advancing sentences
    let commandIterator = params.commandSequence(this.getFocusedPosition(),params.end)[Symbol.iterator]();
    for(let nextCommand = commandIterator.next(); !nextCommand.done; ) {
      const command = nextCommand.value;
      // Do we satisfy the initial condition?
      if(!params.iterateCondition(command, contiguousFocus))
        return;

      // let the command-parsing iterator that we want the next value *NOW*,
      // before we await the command to be added.
      // This is useful for the caller to provide highlighting feedback to the user
      // while we wait for the command to be parsed by Coq
      nextCommand = commandIterator.next();

      const result = await this.addCommand(command,params.verbose);
      contiguousFocus = !result.unfocused;

      // If we have jumped to a new position, create a new iterator since the next command will not be adjacent
      if(result.unfocused)
        commandIterator = params.commandSequence(this.getFocusedPosition(),params.end)[Symbol.iterator](); 
    } // for
  }

  /**
   * Adds a command; assumes that it is adjacent to the current focus
  */
  private async addCommand(command: {text: string, range: Range}, verbose: boolean) : Promise<{sentence: Sentence, unfocused: boolean}> {
    try {
      this.currentError = null;

      const startTime = process.hrtime();
      const parent = this.focusedSentence;
      if(!textUtil.positionIsEqual(parent.getRange().end, command.range.start))
        this.throwInconsistentState("Can only add a comand to the current focus");

      const value = await this.coqtop.coqAddCommand(command.text,this.version,parent.getStateId(),verbose);
      const newSentence = Sentence.add(parent, command.text, value.stateId, command.range, startTime);
      this.sentences.set(newSentence.getStateId(),newSentence);
      // some feedback messages may have arrived before we get here
      this.applyBufferedFeedback();
      newSentence.updateStatus(coqProto.SentenceStatus.ProcessingInput);

      if(textUtil.positionIsAfterOrEqual(newSentence.getRange().start, this.lastSentence.getRange().end))
        this.lastSentence = newSentence;

      if(value.unfocusedStateId) {
        this.setFocusedSentence(this.sentences.get(value.unfocusedStateId));
        // create a new iterator since the next command will not be adjacent
      } else {
        this.setFocusedSentence(newSentence);
      }

      const result =
        { sentence: newSentence
        , unfocused: value.unfocusedStateId == undefined ? false : true
        };        
      return result;
    } catch(error) {
      if(typeof error === 'string')
        throw new InconsistentState(error)
      else if(error instanceof coqtop.CallFailure) {
        const failure = await this.handleCallFailure(error, {range: command.range, text: command.text});
        throw new AddCommandFailure(failure.message, failure.range, failure.range);
      }
      else
        throw error
    } // try
  }

  /**
   * Converts a CallFailure from coqtop (where ranges are w.r.t. the start of the command/sentence) to a FailValue (where ranges are w.r.t. the start of the Coq script).
   */
  private async handleCallFailure(error: coqtop.CallFailure, command: {range: Range, text: string}) : Promise<proto.FailValue> {
    let errorRange : Range = undefined;
    if(error.range) {
        errorRange = vscode.Range.create(
          textUtil.positionAtRelativeCNL(command.range.start, command.text, error.range.start)
        , textUtil.positionAtRelativeCNL(command.range.start, command.text, error.range.stop)
        );
      this.console.log("call failure: " + `${error.range.start}-${error.range.stop}=` + textUtil.rangeToString(errorRange) + " of " + textUtil.rangeToString(command.range) + " (" + command.text + ")");
      this.currentError = {message: error.message, range: errorRange, sentence: command.range}
    } else {
      this.console.log("call failure: " + textUtil.rangeToString(command.range) + " (" + command.text + ")");
    }

    this.currentError = {message: error.message, range: errorRange, sentence: command.range}

    // Some errors tell us the new state to assume
    if(error.stateId)
      await this.gotoErrorFallbackState(error.stateId);
    
    return {message: error.message, range: errorRange, sentence: command.range}
  }

  private parseConvertGoal(goal: coqProto.Goal) : proto.Goal {
    return <proto.Goal>{
      goal: goal.goal,
      hypotheses: goal.hypotheses.map((hyp) => {
        if(hyp.$name === 'richpp') {
          let h = hyp._.$text.split(/(:=|:)([^]*)/);
          return {identifier: h[0].trim(), relation: h[1].trim(), expression: hyp._.$children[0]};
        } else {
          let h = hyp.split(/(:=|:)([^]*)/);
          return {identifier: h[0].trim(), relation: h[1].trim(), expression: h[2].trim()};
        }
      })
    };
  }

  private convertUnfocusedGoals(focusStack: coqProto.UnfocusedGoalStack) : proto.UnfocusedGoalStack {
    if(focusStack)
      return {
        before: focusStack.before.map(this.parseConvertGoal),
        next: this.convertUnfocusedGoals(focusStack.next),
        after: focusStack.after.map(this.parseConvertGoal)
      };
    else
      return null;
  }
  
  private convertGoals(goals: coqtop.GoalResult) : GoalResult {
    switch(goals.mode) {
      case 'no-proof':
        return {type: 'no-proof'}
      case 'proof':
        return {type: 'proof-view',
          goals: goals.goals.map(this.parseConvertGoal),
          backgroundGoals: this.convertUnfocusedGoals(goals.backgroundGoals),
          shelvedGoals: goals.shelvedGoals.map(this.parseConvertGoal),
          abandonedGoals: goals.abandonedGoals.map(this.parseConvertGoal),
        };
      default:
        this.console.warn("Goal returned an unexpected value: " + util.inspect(goals,false,undefined));
    }
  }

  private async gotoErrorFallbackState(stateId: StateId) {
    try {
      const beforeErrorSentence = this.sentences.get(stateId);
      await this.coqtop.coqEditAt(stateId);
      this.rewindTo(beforeErrorSentence);
    } catch(err) {
      this.handleInconsistentState(err);
    }
  }

  private handleInconsistentState(error : any) {
    this.callbacks.coqDied("Inconsistent state: " + error.toString());
    this.dispose();
  }

  private throwInconsistentState(error : string) {
    this.callbacks.coqDied("Inconsistent state: " + error.toString());
    this.dispose();
    throw new InconsistentState(error);
  }

  /**
   * Focuses the sentence; a new sentence may be appended to it
   */
  private async focusSentence(sentence: Sentence) {
    if(sentence == this.focusedSentence)
      return;
    try {
      const result = await this.coqtop.coqEditAt(sentence.getStateId());
      if(result.enterFocus) {
        // Jumping inside an existing proof
        // cancels a range of sentences instead of rewinding everything to this point
        const endStateId = result.enterFocus.qedStateId;
        this.rewindRange(sentence, this.sentences.get(endStateId));
      } else {
        // Rewind the entire document to this point
        this.rewindTo(sentence);
      }
      this.setFocusedSentence(sentence);
    } catch(err) {
      const error = <coqtop.CallFailure>err;
      if(error.stateId)
        await this.gotoErrorFallbackState(error.stateId);
      
    }
  }


  private async cancelSentence(sentence: Sentence) {
    await this.focusSentence(sentence.getParent());
  }

  private deleteSentence(sent: Sentence) {
    this.callbacks.clearSentence(sent.getRange());
    this.sentences.delete(sent.getStateId());
  }

  /** Removes sentences from range (start,end), exclusive; assumes coqtop has already cancelled the sentences  */
  private rewindRange(start: Sentence, end: Sentence) {
    for(let sent of start.removeDescendentsUntil(end))
      this.deleteSentence(sent);
  }

  /** Rewind the entire document to this sentence, range (newLast, ..]; assumes coqtop has already cancelled the sentences  */
  private rewindTo(newLast: Sentence) {
    for(let sent of newLast.descendants())
      this.deleteSentence(sent);
    newLast.truncate();
    this.lastSentence = newLast;
    this.setFocusedSentence(newLast);
  }

  /** Apply buffered feedback to existing sentences, then clear the buffer */    
  private applyBufferedFeedback() {
    // Process any feedback that we may have seen out of order
    this.bufferedFeedback
      .forEach((feedback,i,a) => {
        const sent = this.sentences.get(feedback.stateId);
        if(!sent) {
          this.console.warn("Received buffered feedback for unknown stateId");
          return;
        }
        sent.updateStatus(feedback.status);
        this.callbacks.sentenceStatusUpdate(sent.getRange(), sent.getStatus())
      });
    this.bufferedFeedback = [];
  }

  private setFocusedSentence(sent?: Sentence) {
    if(sent === this.focusedSentence)
      return;
    this.focusedSentence = sent;
    this.callbacks.updateStmFocus(this.getFocusedPosition());
  }

  private onCoqStateStatusUpdate(stateId: number, route: number, status: coqProto.SentenceStatus, worker: string) {
    const sent = this.sentences.get(stateId);
    if(sent) {
      sent.updateStatus(status);
      this.callbacks.sentenceStatusUpdate(sent.getRange(), sent.getStatus())
    } else {
      // Sometimes, feedback will be received before CoqTop has given us the new stateId,
      // So we will buffer these messages until we get the next 'value' response.
      this.bufferedFeedback.push({stateId: stateId, status: status, worker: worker});
    }
  }

  /** A sentence has reached an error state
   * @param location: optional offset range within the sentence where the error occurred
   */
  private onCoqStateError(stateId: number, route: number, message: string, location?: coqProto.Location) {
    const sent = this.sentences.get(stateId);
    if(sent) {
      if(location)
        this.console.log(`CoqStateError: ${location.start}-${location.stop}`);
      sent.setError(message, location);
      this.callbacks.error(sent.getRange(), sent.getError().range, message);
    } else {
      this.console.warn(`Error for unknown stateId: ${stateId}; message: ${message}`);
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

  private onCoqMessage(level: coqProto.MessageLevel, message: string, rich_message?: any) {
    this.callbacks.message(level, message, rich_message);
  }

  private onCoqStateWorkerStatusUpdate(stateId: number, route: number, workerUpdates: coqProto.WorkerStatus[]) {
  }

  private onCoqStateFileDependencies(stateId: number, route: number, fileDependencies: Map<string,string[]>) {
  }

  private onCoqStateFileLoaded(stateId: number, route: number, status: coqProto.FileLoaded) {
  }
  
  private onCoqStateLtacProf(stateId: number, route: number, results: coqProto.LtacProfResults) {
    const sent = this.sentences.get(stateId);
    if(sent) {
      this.callbacks.ltacProfResults(sent.getRange(),results);
    } else {
      this.console.warn(`LtacProf results for unknown stateId: ${stateId}`);
    }
  }
 
  /** recieved from coqtop controller */
  private async onCoqClosed(error?: string) {
    if(!error || !this.running)
      return;
    this.console.log(`onCoqClosed(${error})`);
    this.dispose();
    this.callbacks.coqDied(error);
  }

  private debuggingGetSentences(params?: {begin?: Sentence|string, end?: Sentence|string}) {
    let begin : Sentence, end : Sentence;
    if(params && params.begin === 'focus')
      begin = this.focusedSentence;
    if(!params || !params.begin || typeof params.begin === 'string')
      begin = this.root;
    else
      begin = <Sentence>params.begin;

    if(params && params.end === 'focus')
      end = this.focusedSentence;
    else if(!params || !params.end || typeof params.end === 'string')
      end = this.lastSentence;
    else
      end = <Sentence>params.end;

    const results : DSentence[] = [];
    for(let sent of begin.descendantsUntil(end.getNext())) {
      results.push(createDebuggingSentence(sent));
    }
    Object.defineProperty(this,'__proto__',{enumerable: false});
    return results;
  }



public logDebuggingSentences(ds?: DSentence[], indent: string = '\t') {
  if(!ds)
    ds = this.debuggingGetSentences()
  this.console.log(ds.map((s,idx) => '  ' + (1+idx) + ':\t' + s).join('\n'));  
}

}

// function createDebuggingSentence(sent: Sentence) : {cmd: string, range: string} {
//   const cmd = sent.getText();
//   const range = `${sent.getRange().start.line}:${sent.getRange().start.character}-${sent.getRange().end.line}:${sent.getRange().end.character}`;
//   function DSentence() {
//     this.cmd = cmd;
//     this.range = range;
//     Object.defineProperty(this,'__proto__',{enumerable: false});
//   }
// //  Object.defineProperty(DSentence, "name", { value: cmd });
//   Object.defineProperty(DSentence, "name", { value: "A" });
//   return new DSentence();
// }
function abbrString(s:string) {
  var s2 = coqParser.normalizeText(s);
  if(s2.length > 80)
    return s2.substr(0,80-3) + '...';
  else return s2;
}

type DSentence = string;
function createDebuggingSentence(sent: Sentence) : DSentence {
  return `${sent.getRange().start.line}:${sent.getRange().start.character}-${sent.getRange().end.line}:${sent.getRange().end.character} -- ${abbrString(sent.getText().trim())}`;
}




// class DSentence {
//   public cmd: string;
//   public range: string;
//   constructor(sent: Sentence) {
//     this.cmd = sent.getText();
//     this.range = `${sent.getRange().start.line}:${sent.getRange().start.character}-${sent.getRange().end.line}:${sent.getRange().end.character}`;
//  }
//   public toString() {
//     return this.cmd;
//   }
//   public inspect() {
//     return {cmd: this.cmd, range: this.range}
//   }
// }