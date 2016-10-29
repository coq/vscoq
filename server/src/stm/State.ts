import {Position, Range} from 'vscode-languageserver';
import * as vscode from 'vscode-languageserver';
import * as coqProto from './../coq-proto';
import * as parser from './../parsing/coq-parser';
import * as textUtil from './../util/text-util';
import {Sentence} from './../Sentence';
// import {CoqTopGoalResult} from './protocol';

export type StateId = number;

interface StatusErrorInternal {
  /** Error message */
  message: string,
  /** Range of error within this sentence w.r.t. document positions. Is `undefined` if the error applies to the whole sentence */
  range?: Range,
}

export interface StatusError extends StatusErrorInternal {
  /** Error message */
  message: string,
  /** Range of error within this sentence w.r.t. document positions. Is `undefined` if the error applies to the whole sentence */
  range?: Range,
  /** Range of the sentence containing the error */
  sentence: Range,
}

export enum StateStatus {
  Parsing,
  ProcessingInput,
  Processed,
  InProgress,
  Incomplete,
  Complete,
  Error
}

function convertStatus(status: coqProto.SentenceStatus) : StateStatus {
  switch(status) {
    case coqProto.SentenceStatus.Parsing:          return StateStatus.Parsing;
    case coqProto.SentenceStatus.ProcessingInput:  return StateStatus.ProcessingInput;
    case coqProto.SentenceStatus.Processed:        return StateStatus.Processed;
    case coqProto.SentenceStatus.InProgress:       return StateStatus.InProgress;
    case coqProto.SentenceStatus.Incomplete:       return StateStatus.Incomplete;
    case coqProto.SentenceStatus.Complete:         return StateStatus.Complete;
  }
}

export class State {
  private status: coqProto.SentenceStatus|null;
  // private proofView: CoqTopGoalResult;
  private computeTimeMS: number;
  private error?: StatusErrorInternal = undefined;
  // set to true when a document change has invalidated the meaning of the associated sentence; this state needs to be cancelled
  private markedInvalidated = false;

  private constructor
    ( private commandText: string
    , private stateId: StateId
    , private textRange: Range
    , private prev: State | null
    , private next: State | null
    , private computeStart: [number,number] = [0,0]
  ) {
    this.status = coqProto.SentenceStatus.Parsing;
    // this.proofView = {};
    this.computeTimeMS = 0;
  }

  public static newRoot(stateId: StateId) : State {
    return new State("",stateId,Range.create(0,0,0,0),null,null,[0,0]);
  }

  public static add(parent: State, command: string, stateId: number, range: Range, computeStart : [number,number]) : State {
    // This implies a strict order of descendents by document position
    // To support comments that are not added as sentences,
    // this could be loosened to if(textUtil.isBefore(range.start,parent.textRange.end)).
    if(!textUtil.positionIsEqual(range.start, parent.textRange.end))
      throw "New sentence is expected to be adjacent to its parent";
    const result = new State(command,stateId,range,parent,parent.next,computeStart);
    parent.next = result;
    return result;
  }

  public toString() : string {
    return this.commandText;
  }

  // public remove() {
  //   if(this.next)
  //     this.next.remove();
  //   if(this.prev)
  //     this.prev.next = null;
  //   this.proofView = undefined;
  // }
  public getText() : string {
    return this.commandText;
  }
  public getStateId() : StateId {
    return this.stateId;
  }

  /** Iterates all parent states */
  public *ancestors() : Iterable<State> {
    let state = this.prev;
    while(state != null) {
      yield state;
      state = state.prev;
    }
  }

  /** Iterates all decendent states */
  public *descendants() : Iterable<State> {
    let state = this.next;
    while(state != null) {
      yield state;
      state = state.next;
    }
  }

  /** Iterates all decendent states until, and not including, end */
  public *descendantsUntil(end: StateId|State) : Iterable<State> {
    let state = this.next;
    while(state != null && state.stateId !== end && state !== end) {
      yield state;
      state = state.next;
    }
  }

  /** Iterates this and all ancestor states in the order they appear in the document */
  public *backwards() : Iterable<State> {
    yield this;
    yield *this.ancestors();
  }

  /** Iterates this and all decentant states in the order they appear in the document */
  public *forwards() : Iterable<State> {
    yield this;
    yield *this.descendants();
  }

  public getParent() : State {
    return this.prev;
  }

  public getNext() : State {
    return this.next;
  }

  public truncate() {
    if(this.next)
      this.next.prev = null;
    this.next = null;
  }

  public clear() {
    if(this.prev)
      this.prev.next = this.next;
    if(this.next)
      this.next.prev = this.prev;
  }

  public updateStatus(status: coqProto.SentenceStatus) {
    this.status = status;
  }

  public getRange() : Range {
    return this.textRange;
  }

  /** Adjust's this sentence by the change
   * @returns true if the delta intersects this sentence
  */
  private shift(delta: textUtil.RangeDelta) : boolean {
    this.textRange = textUtil.rangeDeltaTranslate(this.textRange, delta);
    // invalidate if there is an intersection
    return textUtil.rangeIntersects(this.textRange, Range.create(delta.start,delta.end));
  }

  /**
   * Applies the textual changes to the sentence
   * @return false if the change has invalidated the sentence; true if preserved
   */
  public applyTextChanges(changes: vscode.TextDocumentContentChangeEvent[], deltas: textUtil.RangeDelta[], updatedDocumentText: string) : boolean {
    if(this.isRoot())
      return true;

    let newText = this.commandText;
    let newRange = this.textRange;
    let newErrorRange = undefined;
    if(this.error && this.error.range)
      newErrorRange = this.error.range;
    let touchesEnd = false; // indicates whether a change has touched the end of this sentence
    change: for(let idx = 0; idx < changes.length; ++ idx) {
      const change = changes[idx];
      const delta = deltas[idx];
      switch(parser.sentenceRangeContainment(newRange,change.range)) {
        case parser.SentenceRangeContainment.Before:
          newRange = textUtil.rangeDeltaTranslate(newRange,delta);
          if(newErrorRange)
            newErrorRange = textUtil.rangeDeltaTranslate(newErrorRange,delta);
          continue change;
        case parser.SentenceRangeContainment.After:
          if(textUtil.positionIsEqual(this.textRange.end, change.range.start))
            touchesEnd = true;
          continue change; // ignore this change
        case parser.SentenceRangeContainment.Crosses:
          return false; // give up; this sentence is toast (invalidated; needs to be cancelled)
        case parser.SentenceRangeContainment.Contains:
          // the change falls within this sentence
          const beginOffset = textUtil.relativeOffsetAtAbsolutePosition(newText, newRange.start, change.range.start);
          if(beginOffset == -1)
            continue change;
          newText =
            newText.substring(0,beginOffset)
            + change.text
            + newText.substring(beginOffset+change.rangeLength);
          // newRange = Range.create(newRange.start,textUtil.positionRangeDeltaTranslateEnd(newRange.end,delta));
          newRange.end = textUtil.positionRangeDeltaTranslateEnd(newRange.end,delta);

          if(newErrorRange)
            newErrorRange = textUtil.rangeDeltaTranslate(newErrorRange,delta);
      } // switch
    } // change: for


    if(touchesEnd) {
      // We need to reparse the sentence to make sure the end of the sentence has not changed
      const endOffset = textUtil.offsetAt(updatedDocumentText, newRange.end);
      // The problem is if a non-blank [ \r\n] is now contacting the end-period of this sentence; we need only check one more character
      const newEnd = parser.parseSentenceLength(newText + updatedDocumentText.substr(endOffset, 1));
      if(newEnd === -1 || newEnd !== newText.length)
        return false; // invalidate: bad or changed syntax   
    }
    
    if(parser.isPassiveDifference(this.commandText, newText)) {
      this.commandText = newText;
      this.textRange = newRange;
      if(newErrorRange)
        this.error.range = newErrorRange;
      return true;
    } else
      return false;
  }

  public isRoot() : boolean {
    return this.prev === null;
  }

  public markInvalid() : void {
    this.markedInvalidated = true;
  }

  public isInvalidated() : boolean {
    return this.markedInvalidated;
  }

  /** Removes descendents until (and not including) state end */
  public *removeDescendentsUntil(end: State) : Iterable<State> {
    for(let state of this.descendantsUntil(end.stateId))
      yield state;
    // unlink the traversed sentences
    this.next = end;
    end.prev = this;
  }

  public getStatus() : StateStatus {
    if(this.error)
      return StateStatus.Error;
    else
      return convertStatus(this.status);
  }

  public setStatus(status: coqProto.SentenceStatus) : void {
    if(this.status > status)
      return;
    else {
      this.status = status;
      if(this.computeStart && this.status < status) {
        const duration = process.hrtime(this.computeStart);
        this.computeTimeMS = duration[0] * 1000.0 + (duration[1] / 1000000.0);
        // if(status == coqProto.SentenceStatus.Processed)
        //   this.clientConsole.log(`processed in time ${sentence.stateId}: ${sentence.computeTimeMS/1000.0} sec`);
      }      
    }
  }

  /** @returns `true` if this sentence appears strictly before `position` */
  public isBefore(position: Position) : boolean {
    return textUtil.positionIsBeforeOrEqual(this.textRange.end, position);
  }

  /** @returns `true` if this sentence appears before or contains `position` */
  public isBeforeOrAt(position: Position) : boolean {
    return textUtil.positionIsBeforeOrEqual(this.textRange.end, position) || textUtil.positionIsBeforeOrEqual(this.textRange.start, position);
  }

  /** @returns `true` if this sentence appears strictly after `position`. */
  public isAfter(position: Position) : boolean {
    return textUtil.positionIsAfter(this.textRange.start, position);
  }

  /** @returns `true` if this sentence appears after or contains `position`. */
  public isAfterOrAt(position: Position) : boolean {
    return textUtil.positionIsAfterOrEqual(this.textRange.start, position) ||
      textUtil.positionIsAfter(this.textRange.end, position);
  }
  
  /** @returns `true` if this sentence contains `position`. */
  public contains(position: Position) : boolean {
    return textUtil.positionIsBeforeOrEqual(this.textRange.start, position) &&
      textUtil.positionIsAfter(this.textRange.end, position);
  }

  /** This sentence has reached an error state
   * @param location: optional offset range within the sentence where the error occurred
   */
  public setError(message: string, location?: coqProto.Location) : void {
    this.error = {message: message};
    if(location && location.start !== location.stop) {
      const sentRange = this.getRange();
      const sentText = this.getText();
      this.error.range =
        Range.create(
          textUtil.positionAtRelativeCNL(sentRange.start, sentText, location.start),
          textUtil.positionAtRelativeCNL(sentRange.start, sentText, location.stop))
    }
  }

  public getError() : StatusError|null {
    if(this.error) {
      const range = this.getRange();
      return Object.assign(this.error, {sentence: range});
    } else
      return null;
  }

}





