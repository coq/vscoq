

import {Position, Range} from 'vscode-languageserver';
import * as vscode from 'vscode-languageserver';
import * as coqProto from './coq-proto';
import * as parser from './coq-parser';
import * as textUtil from './text-util';
// import {CoqTopGoalResult} from './protocol';

export type StateId = number;

interface SentenceErrorInternal {
  message: string,
  range?: Range,
}

export interface SentenceError extends SentenceErrorInternal {
  message: string,
  range?: Range,
  sentence: Range,
}

export enum SentenceState {
  Parsing,
  ProcessingInput,
  Processed,
  InProgress,
  Incomplete,
  Complete,
  Error
}

function statusToState(status: coqProto.SentenceStatus) : SentenceState {
  switch(status) {
    case coqProto.SentenceStatus.Parsing:          return SentenceState.Parsing;
    case coqProto.SentenceStatus.ProcessingInput:  return SentenceState.ProcessingInput;
    case coqProto.SentenceStatus.Processed:        return SentenceState.Processed;
    case coqProto.SentenceStatus.InProgress:       return SentenceState.InProgress;
    case coqProto.SentenceStatus.Incomplete:       return SentenceState.Incomplete;
    case coqProto.SentenceStatus.Complete:         return SentenceState.Complete;
  }
}

export class Sentence {
  private status: coqProto.SentenceStatus;
  // private proofView: CoqTopGoalResult;
  private computeTimeMS: number;
  private error?: SentenceErrorInternal = undefined;

  private constructor
    ( private commandText: string
    , private stateId: StateId
    , private textRange: Range
    , private prev: Sentence | null
    , private next: Sentence | null
    , private computeStart: [number,number] = [0,0]
  ) {
    this.status = coqProto.SentenceStatus.Parsing;
    // this.proofView = {};
    this.computeTimeMS = 0;
  }

  public static newRoot(stateId: StateId) : Sentence {
    return new Sentence("",stateId,Range.create(0,0,0,0),null,null,[0,0]);
  }

  public static add(parent: Sentence, command: string, stateId: number, range: Range, computeStart : [number,number]) : Sentence {
    // This implies a strict order of descendents by document position
    // To support comments that are not added as sentences,
    // this could be loosened to if(textUtil.isBefore(range.start,parent.textRange.end)).
    if(!textUtil.positionIsEqual(range.start, parent.textRange.end))
      throw "New sentence is expected to be adjacent to its parent";
    const result = new Sentence(command,stateId,range,parent,parent.next,computeStart);
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

  public contains(position: Position) : boolean {
    return textUtil.rangeContains(this.textRange, position);
  }

  public intersects(range: Range) : boolean {
    return textUtil.rangeIntersects(this.textRange, range);
  }

  public isBefore(position: Position) : boolean {
    return textUtil.positionIsBeforeOrEqual(this.textRange.end, position);
  }

  public getStateId() : StateId {
    return this.stateId;
  }

  /** Iterates all parent senteces */
  public *ancestors() : Iterable<Sentence> {
    let sentence = this.prev;
    while(sentence != null) {
      yield sentence;
      sentence = sentence.prev;
    }
  }

  /** Iterates all decendent sentences */
  public *descendants() : Iterable<Sentence> {
    let sentence = this.next;
    while(sentence != null) {
      yield sentence;
      sentence = sentence.next;
    }
  }

  /** Iterates all decendent sentences until. and not including, end */
  public *descendantsUntil(end: StateId|Sentence) : Iterable<Sentence> {
    let sentence = this.next;
    while(sentence != null && sentence.stateId !== end && sentence !== end) {
      yield sentence;
      sentence = sentence.next;
    }
  }

  /** Iterates this and all ancestor sentences in the order they appear in the document */
  public *backwards() : Iterable<Sentence> {
    yield this;
    yield *this.ancestors();
  }

  /** Iterates this and all decentant sentences in the order they appear in the document */
  public *forwards() : Iterable<Sentence> {
    yield this;
    yield *this.descendants();
  }

  public getParent() : Sentence {
    return this.prev;
  }

  public getNext() : Sentence {
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
    this.textRange = textUtil.rangeTranslate(this.textRange, delta);
    // invalidate if there is an intersection
    return textUtil.rangeIntersects(this.textRange, Range.create(delta.start,delta.end));
  }

  /**
   * Applies the textual changes to the sentence
   * @return false if the change has invalidated the sentence; true if preserved
   * 
   * +++***
   * +++_***
   * 1:0-1:3
   * 1:4-1:7
   * @1:3-1:3 insert "_"
   */
  public applyTextChanges(changes: vscode.TextDocumentContentChangeEvent[], deltas: textUtil.RangeDelta[], updatedDocumentText: string) : boolean {
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
          newRange = textUtil.rangeTranslate(newRange,delta);
          if(newErrorRange)
            newErrorRange = textUtil.rangeTranslate(newErrorRange,delta);
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
            newErrorRange.end = textUtil.positionRangeDeltaTranslateEnd(newRange.end,delta);
      } // switch
    } // change: for


    if(touchesEnd) {
      // We need to reparse the sentence to make sure the end of the sentence has not changed
      const endOffset = textUtil.offsetAt(updatedDocumentText, newRange.end);
      // The problem is if a non-blank [ \r\n] is now contacting the end-period of this sentence; we need only check one more character
      const newEnd = parser.parseSentence(newText + updatedDocumentText.substr(endOffset, 1));
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

  /** Removes descendents until (and not including) state end */
  public *removeDescendentsUntil(end: Sentence) : Iterable<Sentence> {
    for(let sent of this.descendantsUntil(end.stateId))
        yield sent;
    // unlink the traversed sentences
    this.next = end;
    end.prev = this;
  }

  public getState() : SentenceState {
    if(this.error)
      return SentenceState.Error;
    else
      return statusToState(this.status);
  }

  public setStatus(status: coqProto.SentenceStatus) {
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

  /** This sentence has reached an error state
   * @param location: optional offset range within the sentence where the error occurred
   */
  public setError(message: string, location?: coqProto.Location) {
    this.error = {message: message};
    if(location && location.start !== location.stop) {
      this.error.range =
        Range.create(
          textUtil.positionAtRelativeCNL(this.textRange.start,this.commandText, location.start),
          textUtil.positionAtRelativeCNL(this.textRange.start,this.commandText, location.stop))
    }
  }

  public getError() : SentenceError|null {
    if(this.error)
      return Object.assign(this.error, {sentence: this.textRange});
    else
      return null;
  }

}





