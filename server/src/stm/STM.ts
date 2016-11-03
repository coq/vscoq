'use strict'

import {Position, Range, TextDocumentContentChangeEvent, TextDocument, RemoteConsole} from 'vscode-languageserver';
import {CancellationToken} from 'vscode-jsonrpc';
import * as vscode from 'vscode-languageserver';
import * as coqProto from './../coqtop/coq-proto';
import * as util from 'util';
import * as proto from './../protocol';
import * as textUtil from './../util/text-util';
import * as coqtop from './../coqtop/coqtop';
import * as coqParser from './../parsing/coq-parser';
import {State, StatusError, StateStatus} from './State';
import {LoadModule, SentenceSemantics} from './../parsing/SentenceSemantics';
import {Mutex} from './../util/Mutex';
import * as server from '../server';

export {StateStatus} from './State';


type StateId = number;

interface BufferedFeedbackBase {
  stateId: number,
}

interface BufferedFeedbackStatus extends BufferedFeedbackBase {
  type: "status",
  status: coqProto.SentenceStatus,
  worker: string,
}

interface BufferedFeedbackFileLoaded extends BufferedFeedbackBase {
  type: "fileLoaded",
  filename: string,
  module: string,
}


type BufferedFeedback = BufferedFeedbackStatus | BufferedFeedbackFileLoaded;

export interface StateMachineCallbacks {
  sentenceStatusUpdate(range: Range, status: StateStatus) : void;
  clearSentence(range: Range) : void;
  updateStmFocus(focus: Position): void;
  error(sentenceRange: Range, errorRange: Range, message: string, rich_message?: any) : void;
  message(level: coqProto.MessageLevel, message: string, rich_message?: any) : void;
  ltacProfResults(range: Range, results: coqProto.LtacProfResults) : void;
  coqDied(error?: string) : void;
}

export type CommandIterator = (begin: Position, end?: Position) => Iterable<{text: string, range: Range}>;

export type GoalErrorResult = proto.NotRunningResult | proto.FailureResult | proto.InterruptedResult
export type GoalResult = proto.NoProofResult | proto.NotRunningResult | proto.BusyResult |
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

class CommandIsBusy {

}

enum STMStatus { Ready, Busy, Interrupting, Shutdown }

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
  private root : State = null;
  // map id to sentence; lazy init  
  private sentences : Map<StateId,State> = null;
  // The sentence that coqtop considers "focused"; lazy init
  private focusedSentence : State = null;
  // The sentence that is closest to the end of the document; lazy init
  private lastSentence : State = null;
  // Handles communication with coqtop
  private coqtop : coqtop.CoqTop;
  // feedback may arrive before a sentence is assigned a stateId; buffer feedback messages for later
  private bufferedFeedback: BufferedFeedback[] = [];
  private documentVersion: number;
  // When it is not prudent to interrupt Coq, e.g. cancelling a sentence:
  private disableInterrupt = false;
  /** The error from the most recent Coq command (`null` if none) */
  private currentError : proto.FailValue = null;
  private status = STMStatus.Ready;
  /** The current state of coq options */
  private currentCoqOptions : coqtop.CoqOptions = {
    printingCoercions: false,
    printingMatching: false,
    printingNotations: true,
    printingExistentialInstances: false,
    printingImplicit: false,
    printingAll: false,
    printingUniverses: false,
  };
  /** Prevent concurrent calls to coqtop */
  private coqLock = new Mutex();
  /** Sequentialize edits */
  private editLock = new Mutex();


  constructor(private settings: proto.CoqTopSettings
    , private scriptFile: string
    , private projectRoot: string
    , private callbacks: StateMachineCallbacks
    , private console: RemoteConsole
  ) {
    this.coqtop = new coqtop.CoqTop(settings, scriptFile, projectRoot, console, {
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
    if(this.status === STMStatus.Shutdown)
      this.console.warn("The STM manager is being disposed before being shut down");
    this.status = STMStatus.Shutdown;
    this.sentences = undefined;
    this.bufferedFeedback = undefined;
    this.console = undefined;
    this.setFocusedSentence(undefined);
    this.callbacks = undefined;
    if(this.coqtop)
      this.coqtop.dispose();
  }

  public async shutdown() {
    if(this.isShutdown())
      return;
    this.status = STMStatus.Shutdown;
    await this.acquireCoq(async () => await this.coqtop.coqQuit());
    this.dispose();
  }

  /**
   * 
  */
  public async interrupt() : Promise<void> {
    if(!this.isBusy() || this.isShutdown())
      return;
    else
      this.status = STMStatus.Interrupting;
    try {
      await this.coqtop.coqInterrupt();
    } catch(err) {
      // this will fail on user interrupt
      this.console.error('Exception thrown while interrupting Coq: ' + err.toString());
    } finally {
      // The command being interrupted should update this.status
      // If not, then it is probably best to kill coqtop via this.shutdown()
      // this.status = STMStatus.Ready
    }
  }

  public isRunning() {
    return this.status !== STMStatus.Shutdown;
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
   * Applies the changes to the sentences
   * @return a list of invalidated sentences -- these need to be cancelled
   */
  private applyChangesToSentences(sortedChanges: TextDocumentContentChangeEvent[], updatedDocumentText: string) : State[] {
    const invalidatedSentences : State[] = [];

    try {
      const deltas = sortedChanges.map((c) => textUtil.toRangeDelta(c.range,c.text))

      if(this.currentError && this.currentError.range) {
        for(let idx = 0; idx < sortedChanges.length; ++idx) {
          this.currentError.range = textUtil.rangeDeltaTranslate(this.currentError.range, deltas[idx])
        }
      }

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
        const preserved = sent.applyTextChanges(sortedChanges,deltas, updatedDocumentText);
        if(!preserved) {
          invalidatedSentences.push(sent);
        }

      } // for sent in ancestors of last sentence
      return invalidatedSentences;
    } catch(err) {
      this.handleInconsistentState(err);
      return [];
    }
  }

  /** Cancel a list of sentences that have (presumably) been invalidated.
   * This will attempt to place the focus just before the topmost cancellation. 
   * @param invalidatedSentences -- assumed to be sorted in descending order (bottom first)
   */
  private async cancelInvalidatedSentences(invalidatedSentences: State[]) : Promise<void> {
    if(invalidatedSentences.length <= 0)
      return;
    // Cancel the invalidated sentences
    const releaseLock = await this.editLock.lock();
    try {
      if(this.status === STMStatus.Busy)
        await this.interrupt();
          // now, this.status === STMStatus.Interrupting until the busy task is cancelled, then it will become STMStatus.Ready

      // Cancel sentences in the *forward* direction
      // // E.g. cancelling the first invalidated sentence may cancel all subsequent sentences,
      // // in which case, the remaining cancellations will become NOOPs
      // for(let idx = invalidatedSentences.length - 1; idx >= 0; --idx) {
      //   const sent = invalidatedSentences[idx];
      for(let sent of invalidatedSentences) {
        await this.cancelSentence(sent);
      }
      // The focus should be at the topmost cancelled sentences 
      this.focusSentence(invalidatedSentences[invalidatedSentences.length-1].getParent());
    } catch(err) {
      this.handleInconsistentState(err);
    } finally {
      releaseLock();
    }
  }

  /** Adjust sentence ranges and cancel any sentences that are invalidated by the edit
   * @param sortedChanges -- a list of changes, sorted by their start position in descending order: later change in doc appears first
   * @returns `true` if no sentences were cancelled
  */
  public applyChanges(sortedChanges: TextDocumentContentChangeEvent[], newVersion: number, updatedDocumentText: string) : boolean {
    if(!this.isRunning() || sortedChanges.length == 0 || this.root === null)
      return true;

    const invalidatedSentences = this.applyChangesToSentences(sortedChanges, updatedDocumentText);
    this.version = newVersion;

    if(invalidatedSentences.length === 0) {
      this.callbacks.updateStmFocus(this.getFocusedPosition())
      return true;
    } else {
      // We do not bother to await this async function
      this.cancelInvalidatedSentences(invalidatedSentences);
      return false;
    }
  }


  /**
   * Adds the next command
   * @param verbose - generate feedback messages with more info
   * @throw proto.FailValue if advancing failed
   */
  public async stepForward(commandSequence: CommandIterator, verbose: boolean = false) : Promise<(proto.FailureResult & proto.FocusPosition)|null>  {
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      await this.validateState(true);
      const currentFocus = this.getFocusedPosition();
      // Advance one statement: the one that starts at the current focus
      await this.iterateAdvanceFocus(
        { iterateCondition: (command,contiguousFocus) => textUtil.positionIsEqual(command.range.start, currentFocus)
        , commandSequence: commandSequence
        , verbose: verbose
        });
      return null;
    } catch (error) {
      if(error instanceof AddCommandFailure)
        return Object.assign(Object.assign(error, <proto.FailureTag>{type: 'failure'}), <proto.FocusPosition>{focus: this.getFocusedPosition()});
      else
        throw error;
    } finally {
      endCommand();
    }
  }

  /**
   * Steps back from the currently focused sentence
   * @param verbose - generate feedback messages with more info
   * @throws proto.FailValue if advancing failed
   */
  public async stepBackward() : Promise<void>  {
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      await this.validateState(false);
      await this.cancelSentence(this.focusedSentence);
    } finally {
      endCommand();
    }
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
    const endCommand = await this.startCommand();
    if(!endCommand)
      return {type: 'busy'};
    try {
      await this.refreshOptions();
      const result = await this.coqtop.coqGoal();
      return this.convertGoals(result);
    } catch(error) {
      if(error instanceof coqtop.CallFailure) {
        const sent = this.focusedSentence;
        const failure = await this.handleCallFailure(error, {range: sent.getRange(), text: sent.getText() });
        return Object.assign(failure, <proto.FailureTag>{type: 'failure'})
      } else
        return this.convertCoqTopError(error)
    } finally {
      endCommand();
    }
  }

  /** Interpret to point
   * Tell Coq to process the proof script up to the given point
   * This may not fully process everything, or it may rewind the state.
   * @throws proto.FailValue if advancing failed
   */
  public async interpretToPoint(position: Position, commandSequence: CommandIterator, token: CancellationToken) : Promise<(proto.FailureResult & proto.FocusPosition)|null> {
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      await this.validateState(true);
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

      return null;
    } catch (error) {
      if(error instanceof AddCommandFailure)
        return Object.assign(Object.assign(error, <proto.FailureTag>{type: 'failure'}), <proto.FocusPosition>{focus: this.getFocusedPosition()});
      else
        throw error;
    } finally {
      endCommand();
    }
  }

  public async doQuery(query: string, position?: Position) : Promise<string> {
    if(!this.isCoqReady())
      return "";
    const endCommand = await this.startCommand();
    if(!endCommand)
      return "";
    try {
      let state: StateId = undefined;
      if(position)
        state = this.getParentSentence(position).getStateId();
      await this.refreshOptions();
      return await this.coqtop.coqQuery(query, state)
    } finally {
      endCommand();
    }
  }

  public async setWrappingWidth(columns: number) : Promise<void> {
    if(!this.isCoqReady())
      return;
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      this.coqtop.coqResizeWindow(columns);
    } catch(error) {
      this.console.warn("error resizing window: " + error.toString())
    } finally {
      endCommand();
    }
  }

  public async requestLtacProfResults(position?: Position) : Promise<void> {
    if(!this.isCoqReady())
      return;
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      if(position !== undefined) {
        const sent = this.getSentence(position);
        if(sent) {
          await this.coqtop.coqLtacProfilingResults(sent.getStateId());
          return;
        }
      }
      await this.coqtop.coqLtacProfilingResults();
    } finally {
      endCommand();
    }
  }
  //     ltacProfResults: (offset?: number) => this.enqueueCoqOperation(async () => {
  //       if(offset) {
  //         const sent = this.sentences.findAtTextPosition(offset);
  //         return this.coqTop.coqLtacProfilingResults(sent===null ? undefined : sent.stateId);
  //       } else
  //         return this.coqTop.coqLtacProfilingResults();
  //     }, true),


  public async setDisplayOptions(options: {item: proto.DisplayOption, value: proto.SetDisplayOption}[]) {
    function set(old: boolean, change: proto.SetDisplayOption) : boolean {
      switch(change) {
        case proto.SetDisplayOption.On: return true;
        case proto.SetDisplayOption.Off: return false;
        case proto.SetDisplayOption.Toggle: return !old;
      }
    }
    for(let option of options) {
      switch(option.item) {
        case proto.DisplayOption.AllLowLevelContents: {
          // for toggle: on-->off iff all are on; off->on iff any are off
          const value = set(this.currentCoqOptions.printingAll && this.currentCoqOptions.printingExistentialInstances && this.currentCoqOptions.printingUniverses, option.value)
          this.currentCoqOptions.printingAll = value;
          this.currentCoqOptions.printingExistentialInstances = value;
          this.currentCoqOptions.printingUniverses = value;
          break;
        }
        case proto.DisplayOption.AllBasicLowLevelContents:
          this.currentCoqOptions.printingAll = set(this.currentCoqOptions.printingAll, option.value);
          break; 
        case proto.DisplayOption.Coercions:
          this.currentCoqOptions.printingCoercions = set(this.currentCoqOptions.printingCoercions, option.value);
          break; 
        case proto.DisplayOption.ExistentialVariableInstances:
          this.currentCoqOptions.printingExistentialInstances = set(this.currentCoqOptions.printingExistentialInstances, option.value);
          break; 
        case proto.DisplayOption.ImplicitArguments:
          this.currentCoqOptions.printingImplicit = set(this.currentCoqOptions.printingImplicit, option.value);
          break; 
        case proto.DisplayOption.Notations:
          this.currentCoqOptions.printingNotations = set(this.currentCoqOptions.printingNotations, option.value);
          break; 
        case proto.DisplayOption.RawMatchingExpressions:
          this.currentCoqOptions.printingMatching = set(this.currentCoqOptions.printingMatching, option.value);
          break; 
        case proto.DisplayOption.UniverseLevels:
          this.currentCoqOptions.printingUniverses = set(this.currentCoqOptions.printingUniverses, option.value);
          break; 
      }
    }
    //await this.setCoqOptions(this.currentCoqOptions);
  }

  private async setCoqOptions(options: coqtop.CoqOptions) {
    if(!this.isCoqReady())
      return;
    const endCommand = await this.startCommand();
    if(!endCommand)
      return;
    try {
      await this.coqtop.coqSetOptions(options);
    } finally {
      endCommand();
    }
  }


  public *getSentences() : Iterable<{range: Range, status: StateStatus}> {
    if(!this.isRunning() || this.root===null)
      return;
    for(let sent of this.root.descendants())
      yield { range: sent.getRange(), status: sent.getStatus()}
  }

  public *getSentenceErrors() : Iterable<StatusError> {
    if(!this.isRunning() || this.root===null)
      return;
    for(let sent of this.root.descendants()) {
      if(sent.getError())
        yield sent.getError();
    }
  }

  public *getErrors() : Iterable<StatusError> {
    if(!this.isRunning() || this.root===null)
      return;
    yield *this.getSentenceErrors();
    if(this.currentError !== null)
      yield this.currentError;
  }

  private getParentSentence(position: Position) : State {
    for(let sentence of this.root.descendants()) {
      if(!sentence.isBefore(position))
        return sentence.getParent();
    }
    // This should never be reached
    return this.root;
  }

  private getSentence(position: Position) : State {
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
    if(!this.isRunning())
      throw "Cannot reinitialize the STM once it has died; create a new one."
    this.root = State.newRoot(rootStateId);
    this.sentences = new Map<StateId,State>([ [this.root.getStateId(),this.root] ]);
    this.lastSentence = this.root;
    this.setFocusedSentence(this.root);
  }

  /** Assert that we are in a "running"" state
   * @param initialize - initialize Coq if true and Coq has not yet been initialized
   * @returns true if it is safe to communicate with coq
  */
  private isCoqReady() : boolean {
    return this.isRunning() && this.coqtop.isRunning();
  }

  /** Assert that we are in a "running"" state
   * @param initialize - initialize Coq if true and Coq has not yet been initialized
   * @returns true if it is safe to communicate with coq
  */
  private async validateState(initialize: boolean) : Promise<boolean> {
    if(!this.isRunning() && initialize)
      throw "Cannot perform operation: coq STM manager has been shut down."
    else if(!this.isRunning())
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
  private async addCommand(command: {text: string, range: Range}, verbose: boolean) : Promise<{sentence: State, unfocused: boolean}> {
    try {
      this.currentError = null;

      const startTime = process.hrtime();
      const parent = this.focusedSentence;
      if(!textUtil.positionIsEqual(parent.getRange().end, command.range.start))
        this.throwInconsistentState("Can only add a comand to the current focus");

      const value = await this.coqtop.coqAddCommand(command.text,this.version,parent.getStateId(),verbose);
      const newSentence = State.add(parent, command.text, value.stateId, command.range, startTime);
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
    if(error.range)
      errorRange = vscode.Range.create(
        textUtil.positionAtRelativeCNL(command.range.start, command.text, error.range.start)
      , textUtil.positionAtRelativeCNL(command.range.start, command.text, error.range.stop)
      );

    this.currentError = {message: error.message, range: errorRange, sentence: command.range}

    // Some errors tell us the new state to assume
    if(error.stateId !== undefined && error.stateId != 0)
      await this.gotoErrorFallbackState(error.stateId);
    
    return {message: error.message, range: errorRange, sentence: command.range}
  }

  private parseConvertGoal(goal: coqProto.Goal) : proto.Goal {
    return <proto.Goal>{
      goal: server.project.getPrettifySymbols().prettify(goal.goal),
      hypotheses: goal.hypotheses.map((hyp) => {
        let h = (hyp as string).split(/(:=|:)([^]*)/);
        return {identifier: h[0].trim(), relation: h[1].trim(), expression: server.project.getPrettifySymbols().prettify(h[2].trim())};
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
        const result : GoalResult = {type: 'proof-view',
          goals: goals.goals.map(this.parseConvertGoal),
          backgroundGoals: this.convertUnfocusedGoals(goals.backgroundGoals),
          shelvedGoals: goals.shelvedGoals.map(this.parseConvertGoal),
          abandonedGoals: goals.abandonedGoals.map(this.parseConvertGoal),
        };
        this.focusedSentence.setGoal(result);
        return result;
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
   * Focuses the sentence; a new sentence may be appended to it.
   * @param sentence -- does nothing if null, already the focus, or its state ID does not exist
   */
  private async focusSentence(sentence?: State) {
    if(!sentence || sentence == this.focusedSentence || !this.sentences.has(sentence.getStateId()))
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


  private async cancelSentence(sentence: State) {
    if(!this.sentences.has(sentence.getStateId()))
      return;
    await this.focusSentence(sentence.getParent());
  }

  private deleteSentence(sent: State) {
    this.callbacks.clearSentence(sent.getRange());
    this.sentences.delete(sent.getStateId());
  }

  /** Removes sentences from range (start,end), exclusive; assumes coqtop has already cancelled the sentences  */
  private rewindRange(start: State, end: State) {
    for(let sent of start.removeDescendentsUntil(end))
      this.deleteSentence(sent);
  }

  /** Rewind the entire document to this sentence, range (newLast, ..]; assumes coqtop has already cancelled the sentences  */
  private rewindTo(newLast: State) {
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
          this.console.warn("Received buffered feedback for unknown stateId: " + feedback.stateId);
          return;
        }
        if(feedback.type === "status") {
          sent.updateStatus(feedback.status);
          this.callbacks.sentenceStatusUpdate(sent.getRange(), sent.getStatus())
        } else if(feedback.type === "fileLoaded") {
          // if(sent.getText().includes(feedback.module))
          //   sent.addSemantics(new LoadModule(feedback.filename, feedback.module));
        }
      });
    this.bufferedFeedback = [];
  }

  private setFocusedSentence(sent?: State) {
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
      this.bufferedFeedback.push({stateId: stateId, type: "status", status: status, worker: worker});
    }
  }

  /** A sentence has reached an error state
   * @param location: optional offset range within the sentence where the error occurred
   */
  private onCoqStateError(stateId: number, route: number, message: string, location?: coqProto.Location) {
    const sent = this.sentences.get(stateId);
    if(sent) {
      // if(location)
      //   this.console.log(`CoqStateError: ${location.start}-${location.stop}`);
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
    // const sent = this.sentences.get(stateId);
    // if(sent) {
    //   if(sent.getText().includes(status.module))
    //     sent.addSemantics(new LoadModule(status.filename, status.module));
    // } else {
    //   this.bufferedFeedback.push({stateId: stateId, type: "fileLoaded", filename: status.filename, module: status.module});
    // }
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
    if(!error || !this.isRunning())
      return;
    this.console.log(`onCoqClosed(${error})`);
    this.dispose();
    this.callbacks.coqDied(error);
  }

  private async startCommand() : Promise<false | (()=>void)> {
    if(this.isBusy())
      return false
    const release = await this.coqLock.lock();
    this.status = STMStatus.Busy;
    return () => {
      this.status = STMStatus.Ready
      release();
    };
  }

  private isBusy() {
    return this.status === STMStatus.Busy || this.status === STMStatus.Interrupting || this.editLock.isLocked();
  }

  private isShutdown() {
    return this.status === STMStatus.Shutdown
  }

  private isInterrupting() {
    return this.status === STMStatus.Interrupting
  }

  private async acquireCoq<T>(callback: () => T): Promise<T> {
    const release = await this.coqLock.lock();
    try {
      return callback();
    } finally {
      release();
    }
  }

  private debuggingGetSentences(params?: {begin?: State|string, end?: State|string}) {
    let begin : State, end : State;
    if(params && params.begin === 'focus')
      begin = this.focusedSentence;
    if(!params || !params.begin || typeof params.begin === 'string')
      begin = this.root;
    else
      begin = <State>params.begin;

    if(params && params.end === 'focus')
      end = this.focusedSentence;
    else if(!params || !params.end || typeof params.end === 'string')
      end = this.lastSentence;
    else
      end = <State>params.end;

    const results : DSentence[] = [];
    for(let sent of begin.descendantsUntil(end.getNext())) {
      results.push(createDebuggingSentence(sent));
    }
    Object.defineProperty(this,'__proto__',{enumerable: false});
    return results;
  }

  private async refreshOptions() : Promise<void> {
    let options : coqtop.CoqOptions = {};
    options.printingWidth = this.currentCoqOptions.printingWidth;
    options.printingCoercions = this.currentCoqOptions.printingCoercions;
    options.printingMatching = this.currentCoqOptions.printingMatching;
    options.printingNotations = this.currentCoqOptions.printingNotations;
    options.printingExistentialInstances = this.currentCoqOptions.printingExistentialInstances;
    options.printingImplicit = this.currentCoqOptions.printingImplicit;
    options.printingAll = this.currentCoqOptions.printingAll;
    options.printingUniverses = this.currentCoqOptions.printingUniverses;
    await this.coqtop.coqSetOptions(options);
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
function createDebuggingSentence(sent: State) : DSentence {
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