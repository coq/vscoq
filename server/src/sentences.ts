'use strict';

import * as coqProto from './coq-proto';

/*

interpreting multiple lines:
  send multiple messages
  only send Goal request after batch

"route"???

After Add:
  <- values
  <- feedback: processingin, by: (ex:"master"), for: state_id
  <- feedback: processed
  <- feedback: inprogress, int:1 ?????? (not always emitted; called for "intros." after "processed")
  <- feedback: incomplete, for: state_id, after "processing", for: "Qed."
  <- feedback: complete, for: state_id (e.g. "Qed."), after "incomplete"

call "Status"
<-value:
  "good"
  status: [Top], Some lemmaName1, lemmaName2, 0

when there is a tactic error in the middle,
interpreting to that point will cause an Edit_at for the error sentence
<-value "fail"
then Edit_at for the previous sentence
<-value "good":
  inR: (editAt:stateId,(qedAfterEdit:stateId,qedForNextLemma:stateId))


*/


export interface Sentence {
  stateId: number;
  editId: number;
  textBegin: number;
  textEnd: number;
  status: coqProto.SentenceStatus;
}

class SentenceLink implements Sentence {
  stateId: number;
  editId: number;
  textBegin: number;
  textEnd: number;
  status: coqProto.SentenceStatus;
  private previous: SentenceLink = null;
  private next : SentenceLink = null;
  constructor(previous:SentenceLink,stateId:number, textBegin:number, textEnd:number) {
    this.stateId = stateId; this.textBegin = textBegin; this.textEnd = textEnd;
    this.previous = previous;
    this.status = coqProto.SentenceStatus.Parsed;
  }
  static createRoot(stateId:number) : SentenceLink {
    return new SentenceLink(null,stateId,0,0);
  }
  static createNext(parent: SentenceLink, stateId: number, textBegin:number, textEnd: number) : SentenceLink {
    const next = new SentenceLink(parent,stateId,textBegin,textEnd);
    if(parent.next != null)
      throw "Parent sentence already has child";
    parent.next = next;
    return next;
  }
  public getParent() {
    return this.previous;
  }
  public getChild() : SentenceLink {
    return this.next;
  }
  public *descendents() : Iterable<SentenceLink> {
    let child = this.next;
    while(child!==null) {
      yield child;
      child = child.next;
    }
  }
  public rewindToHere() {
    this.next = null;
  }
  public toString() : string {
    return `{${this.stateId}, [${this.textBegin},${this.textEnd})}`;
  } 
}

export class Sentences {
  private sentences = new Map<number,SentenceLink>();
  private sentencesByPosition : SentenceLink[] = [];
  
  // A stack of the current edit-points; the top is the current tip, and when it is done, it will be popped and the next tip will be at top 
  // assume:
  //  - tips are always in sentences (if sentences is not empty)
  //  - tips have no children
  private tip : SentenceLink = null;
  
  constructor() {
  }
  
  public getTip() : Sentence {
    if(!this.tip)
      throw "Coq not initialized";
    return this.tip;
  }

  public setTip(newTipId : number) : void {
    this.tip = this.sentences.get(newTipId);
  }
  
  public hasTip() : boolean {
    return this.tip != null;
  }

  private removeDescendants(sent: SentenceLink,sentLast?: Sentence) {
    for(let child of sent.descendents()) {
      this.sentences.delete(child.stateId);
      
      // TODO: this is probably not efficient; we may be able to simoplify things once we understand exactly when a sentence may have multiple children
      this.sentencesByPosition.splice(this.sentencesByPosition.indexOf(child),1);

      if(sentLast && child.stateId===sentLast.stateId)
        return;
    }
  }
  
  public toString() {
    return this.sentencesByPosition.toString();
  }

  public rewindToWithLast(sentenceTo: Sentence, sentenceLast: Sentence) : Sentence {
    if(sentenceTo === null || sentenceLast === null)
      throw "Invalid sentences";
    const sentTo = this.sentences.get(sentenceTo.stateId);
    const sentLast = this.sentences.get(sentenceLast.stateId);
    if(sentTo === undefined || sentLast===undefined)
      throw "Sentence is an orphan";
      
    this.removeDescendants(sentTo, sentLast);
    
    // remove any tips that have been undone and push the new tip    
    this.tip = sentTo;

    sentTo.rewindToHere();
    return sentenceTo;
  }
  
  public rewindTo(sentence: Sentence) : Sentence {
    if(sentence === null)
      throw "Invalid sentence";
    const sent = this.sentences.get(sentence.stateId);
    if(sent === undefined)
      throw "Sentence is an orphan";
      
    this.removeDescendants(sent);
    
    // remove any tips that have been undone and push the new tip    
    this.tip = sent;

    sent.rewindToHere();
    return sentence;
  }
  
  public rewindOnceFrom(sentence : Sentence) : Sentence {
    if(sentence === null)
      throw "Invalid sentence";
    const sent = this.sentences.get(sentence.stateId);
    if(sent === undefined)
      throw "Sentence is an orphan";
    if(sent.getParent() === null)
      return null;

    this.removeDescendants(sent);
    this.sentences.delete(sent.stateId);
    this.sentencesByPosition.splice(this.sentencesByPosition.indexOf(sent),1);

    // remove any tips that have been undone and push the new tip    
    this.tip = sent.getParent();

    sent.getParent().rewindToHere();
    return sent.getParent();
  }

  /**
   * case:  [A] X [B]  --> A
   * case:  [A-X] [B]  --> A
   * @returns the positional index of the sentence at or before the position (positional indices are used for this.sentencesByPosition)
   */
  private positionalIndexAt(position: number, begin?: number, end?: number) : number {
    // binary search!
    if(begin == undefined)
      begin = 0;
    if(end == undefined)
      end = this.sentencesByPosition.length;
    while (begin < end) {
      const pivot = (begin + end) >> 1;
      const pivotSent = this.sentencesByPosition[pivot];
      if(position < pivotSent.textBegin)
        end = pivot;
      else if(position < pivotSent.textEnd)
        return pivot;
      else if (begin == pivot)
        return begin;
      else
        begin = pivot;
    }
    return begin;
  }

  /**
   * @returns either the sentence that contains the position or else null
   */
  public findAtTextPosition(position: number) : Sentence {
    const sent = this.sentencesByPosition[this.positionalIndexAt(position)];
    if(position < sent.textEnd)
      return sent;
    else
      return null;
  }
  

  public addChild(parent: Sentence, stateId:number, textBegin:number, textEnd: number) : Sentence {
    if(!parent)
      throw "Invalid parent";
    const p = this.sentences.get(parent.stateId);
    if(!parent || p === undefined)
      throw "Invalid parent";
    if(this.sentences.has(stateId))
      throw "Duplicate state-id";

    const child = SentenceLink.createNext(p,stateId,textBegin,textEnd);

    this.tip = child;
    
    this.sentences.set(stateId, child);

    // insert this child by position
    const insertIdx = this.positionalIndexAt(child.textBegin);    
    // ASSUME: the child does not intersect with any preexisting sentence
    this.sentencesByPosition.splice(insertIdx+1,0,child);

    return child;
  }
  
  public getPredecessor(sentence: Sentence) : Sentence {
    if(sentence === null)
      throw "Invalid sentence";
    const sent : SentenceLink = this.sentences.get(sentence.stateId);
    if(sent === undefined)
      throw "Invalid sentence";
    return sent.getParent();
  }
  
  public get(stateId: number) : Sentence {
    return this.sentences.get(stateId);
  }
  
  public reset(stateId: number) : void {
    this.sentences.clear();
    const root = SentenceLink.createRoot(stateId);
    this.sentences.set(stateId, root);
    this.sentencesByPosition = [root];
    this.tip = root;
  }
  
  private *getSentenceByPositionIterator(beginIdx: number, endIdx: number) : Iterable<Sentence> {
    for(let idx = beginIdx; idx < endIdx; ++idx)
      yield this.sentencesByPosition[idx];
  }

  /** Returns an ordered list of sentences that intersect the range
   * @param begin start of range
   * @param end end of range
   * @returns the sentences that contain and lie between begin and end (textual positioning)
   */
  public *getRange(beginPos: number, endPos: number) : Iterable<Sentence> {
    const beginIdx = this.positionalIndexAt(beginPos,undefined,endPos);
    const endIdx = this.positionalIndexAt(endPos,beginPos,undefined);
    return this.getSentenceByPositionIterator(beginIdx,endIdx);
  }
  
  public getRangeAffected(beginPos: number, endPos: number) : {length:number,affected:Iterable<Sentence>} {
    let beginIdx = this.positionalIndexAt(beginPos);
    if(beginIdx >= this.sentencesByPosition.length)
      return {length: 0, affected: []};
      
    let endIdx = this.positionalIndexAt(endPos,beginIdx);
    // endIdx includes the position, so take the next sentence
    ++endIdx;
    // beginIdx might come before beginPos, so check whether to include it
    if(this.sentencesByPosition[beginIdx].textEnd <= beginPos)
      ++beginIdx;
    endIdx = Math.max(beginIdx, endIdx);
    return {
      length: Math.max(0,endIdx-beginIdx),
      affected: this.getSentenceByPositionIterator(beginIdx,endIdx)
    };
  }
  
  // Increases or decreases the number of characters in a sentence at position and adjusts all subsequent sentences
  public shiftCharacters(position: number, count: number) : boolean {
    if(count == 0)
      return;
    const beginIdx = this.positionalIndexAt(position);
    const beginSent = this.sentencesByPosition[beginIdx];
    if(beginSent.textEnd > position) {
      // contains the position
      if(-count > beginSent.textEnd - beginSent.textBegin)
        return false; // cannot remove more characters than a sentence has
      beginSent.textEnd += count;
    } else if(beginIdx < this.sentencesByPosition.length-1
      && -count > this.sentencesByPosition[beginIdx+1].textBegin-beginSent.textEnd) {
      return false; // cannot remove more characters than exist between sentences      
    }
    
    // shift subsequent sentences
    for (let idx = beginIdx+1; idx < this.sentencesByPosition.length; ++idx) {
      this.sentencesByPosition[idx].textBegin+= count;
      this.sentencesByPosition[idx].textEnd+= count;
    }
    
    return true;
  }

  private positionalIndexPreceding(offset: number) : number {
    const idx = this.positionalIndexAt(offset);
    if(idx <= 0)
      return 0;
    else if(this.sentencesByPosition[idx].textEnd < offset)
      return idx;
    else // idx intersects, so return previous
      return idx - 1;
  }
  public findPrecedingSentence(offset: number) : Sentence {
    const sentIdx = this.positionalIndexPreceding(offset);
    if(sentIdx === -1)
      return null;
    return this.sentencesByPosition[sentIdx];    
  }
// 
//   public beginEditAt(offset: number) : Sentence {
//     // find the sentence that immediately precedes the offset
//     const sentIdx = this.positionalIndexPreceding(offset);
//     if(sentIdx === -1)
//       return null;
// 
//     return this.sentencesByPosition[sentIdx];    
//   }  
//   
  
}
