import * as textUtil from './text-util'
import {Position, Range} from 'vscode-languageserver';
import * as vscode from 'vscode-languageserver';
import {Sentence} from './Sentence';
import * as parser from './coq-parser';
import {TextDocumentItem} from './document'
import * as server from './server'


export type SentencesInvalidatedCallback = (invalidatedSentences: Sentence[]) => void; 


export class SentenceCollection implements vscode.TextDocument {
  private sentences: Sentence[] = [];
  private sentencesInvalidatedCallbacks = new Set<SentencesInvalidatedCallback>();
  
  public languageId: string = 'coq';
  public lineCount : number = 0;
  public uri: string;
  public version: number;
  private documentText: string;

  public constructor(document: TextDocumentItem) {
    this.uri = document.uri;
    this.version = document.version;
    this.documentText = document.text;
    this.lineCount = textUtil.positionAt(document.text, document.text.length-1).line;
    try {
      this.reparseSentences(0);
    } catch(err) {
      server.connection.console.error(err);
    }
  }

  private applyChangesToDocumentText(sortedChanges: vscode.TextDocumentContentChangeEvent[]) : void {
    for(const change of sortedChanges) {
      const beginOffset = textUtil.offsetAt(this.documentText, change.range.start);
      this.documentText =
        this.documentText.substring(0,beginOffset)
        + change.text
        + this.documentText.substring(beginOffset+change.rangeLength);

      const delta = textUtil.toRangeDelta(change.range, change.text);
      this.lineCount += delta.linesDelta;
    }
  }

  public getText() : string {
    return this.documentText;
  }

  public positionAt(offset: number) : Position {
    for(let sent of this.sentences) {
      const sentOffset = sent.getDocumentEndOffset();
      if(sent.getDocumentOffset() <= offset && offset < sentOffset) {
        return sent.positionAt(offset - sentOffset);
      }
    }
    // Can't find the offset in a sentence, so calculate the position from the whole document
    return textUtil.positionAt(this.documentText, offset);
  }

  public offsetAt(position: Position) : number {
    const sentIdx = this.getSentenceIndexBeforeOrAt(position);
    if(sentIdx < 0 || this.sentences[sentIdx].isBefore(position))
      return textUtil.offsetAt(this.documentText, position);
    else
      return this.sentences[sentIdx].documentOffsetAt(position);
  }

  public onSentencesInvalidated(handler: SentencesInvalidatedCallback) : { dispose: () => void } {
    this.sentencesInvalidatedCallbacks.add(handler);
    return { dispose: () => {
      this.sentencesInvalidatedCallbacks.delete(handler);
    }}
  }

  /** 
   * @returns the index of the closest sentence containing or appearing before `pos`, or `-1` if no sentence is before or contains `pos`. 
   */
  private getSentenceIndexBeforeOrAt(pos: Position) : number {
    let sentIdx = 0;
    while(sentIdx < this.sentences.length && this.sentences[sentIdx].isBeforeOrAt(pos))
      ++sentIdx;
    if(sentIdx >= this.sentences.length)
      return -1;
    else
      return sentIdx-1;
  }

  /** 
   * @returns the index of the closest sentence containing or appearing after `pos`, or `this.sentences.length` if no sentence is after or contains `pos`. 
   */
  private getSentenceIndexAfterOrAt(pos: Position) : number {
    if(this.sentences.length === 0)
      return 0;
    let sentIdx = this.sentences.length - 1;
    while(sentIdx >= 0 && this.sentences[sentIdx].isAfterOrAt(pos))
      --sentIdx;
    return sentIdx+1;
  }

  /**
   * Applies text changes to the sentences; adjusting ranges and possibly invalidating sentences.
   * Invalidated sentences will be automatically reparsed.
   */
  public applyTextChanges(newVersion: number, changes: vscode.TextDocumentContentChangeEvent[]) {
    // sort the edits such that later edits are processed first
    let sortedChanges =
      changes.sort((change1,change2) =>
        textUtil.positionIsAfter(change1.range.start, change2.range.start) ? -1 : 1)

    this.applyChangesToDocumentText(changes);

    const invalidatedSentences : number[] = [];
    const deltas = sortedChanges.map((c) => textUtil.toRangeDelta(c.range,c.text))
    for(let sentIdx = this.sentences.length-1; sentIdx >= 0; --sentIdx) {
      const sent = this.sentences[sentIdx];

      const preserved = sent.applyTextChanges(sortedChanges,deltas,this.documentText);
      if(!preserved) {
        invalidatedSentences.push(sentIdx);
      }
    }

    this.version = newVersion;
    const removed = this.reparseSentencesByIndices(invalidatedSentences);
    this.sentencesInvalidatedCallbacks.forEach((handler) => handler(removed.removed));
  }


  /**
   * @param count -- minimum number of sentences to reparse
   * @return reparsed sentences
   */
  private reparseSentencesByIndices(indices: number[]) : {removed: Sentence[], added: Sentence[]} {
    if(indices.length <= 0)
      return {removed: [], added: [] };

    // sort in ascending order
    indices = indices.sort();

    const removed : Sentence[] = [];
    const added : Sentence[] = [];
    let shift = 0;
    for(let idx = 0; idx < indices.length; ++idx) {
      const sentIdx = shift + indices[idx];
      const patch = this.reparseSentences(sentIdx);
      removed.push(...patch.removed);
      added.push(...patch.added);

      if(patch.endOfSentences)
        break;

      // skip past any indices that were reparsed in this patch
      while(idx < indices.length && shift+indices[idx] < sentIdx + patch.removed.length)
        ++idx;

      // removing & inserting parsed sentences will cause `indices` to drift w.r.t. `this.sentences`
      // this tracks the adjustments for indices past our current point
      // (but is not accurate for `< idx`)
      shift+= patch.added.length - patch.removed.length;
    }

    return {removed: removed, added: added}
  }

//   /**
//    * @param count -- minimum number of sentences to reparse
//    * @return reparsed sentences
//    */
//   private reparseSentencesByIndices(indices: number[]) : Sentence[] {
//     if(indices.length <= 0)
//       return [];

//     // sort in ascending order
//     indices = indices.sort();
//     let indicesIdx = 0;

//     let startIdx = indices[indicesIdx]; 

//     let indexShift = 0;

//     // position of next sentence to be reparsed
//     let currentPosition = this.sentences[startIdx].getRange().end;
//     // offset of next sentence to be reparsed
//     let currentOffset = this.sentences[startIdx].getDocumentOffset();
//     // New sentences
//     let reparsed : Sentence[] = [];
//     // all sentences that have been removed
//     const removed : Sentence[] = [];
//     //
//     let compareNextIdx = startIdx+1;
//     // start at the first index and reparse all subsequent indices;
//     // if no reparse is necessary, then jump to the next unreparsed index in `indices`
//     for(let idx = startIdx; idx < this.sentences.length; ++idx) {
//       // Advance to the next existing sentence that we may traverse next
//       // we will use this to determine if we can stop reparsing sentences
//       while(compareNextIdx < this.sentences.length && currentOffset >= this.sentences[compareNextIdx].getDocumentOffset())
//         ++compareNextIdx;

//       const parseText = this.documentText.substring(currentOffset);
//       const len = parser.parseSentence(parseText);

//       if(len <= 0) {
//         // end of parsable sentences
//         // treat the rest of the document as unparsed
//         const removedPatch = this.sentences.splice(startIdx, this.sentences.length - startIdx, ...reparsed);
//         removed.push(...removedPatch);
//         return removed;
//       }
//       else if(compareNextIdx < this.sentences.length && currentOffset+len === this.sentences[compareNextIdx].getDocumentOffset()) {
//         // no need to parse further.. try the next index in indices
//         // replace reparsed sentences
//         // keep remaining sentences until next index in `indices`

//         // advance to the next index in indices
//         // skip past any that we may already reparsed
//         while(indicesIdx < indices.length && idx >= indexShift+indices[indicesIdx])
//           ++indicesIdx;

//         // replace the sentence patch with what we've reparsed them as
//         const removedPatch = this.sentences.splice(startIdx, idx-startIdx, ...reparsed)
//         // indices in `indices` need to be shifted to properly map to elements
//         // in `this.sentences`
//         indexShift += reparsed.length - removedPatch.length;
//         removed.push(...removedPatch);
// //sdfasdfasdfasdfasdfasdf

//         if(indicesIdx >= indices.length) {

//         } else
//           startIdx = indexShift+indices[indicesIdx]; 
//       }

//       const command = parseText.substring(0, len);
//       const range = Range.create(currentPosition, textUtil.positionAtRelative(currentPosition, command, len));
//       reparsed.push(new Sentence(command, range, currentOffset));
//       currentPosition = range.end;
//       currentOffset+= len;

//     }
//   }


  /**
   * @param count -- minimum number of sentences to reparse
   * @return removed sentences
   */
  private reparseSentences(start: number, minCount: number = 0) : {removed: Sentence[], added: Sentence[], endOfSentences: boolean} {
    if(start < 0 || start > this.sentences.length)
      throw new RangeError("sentence index out of range");
    else if(minCount > this.sentences.length - start)
      minCount = this.sentences.length - start;

    let currentPosition : Position;
    let currentOffset : number;
    if(this.sentences.length === 0) {
      currentPosition = Position.create(0,0);
      currentOffset = 0;
    } else if(start < this.sentences.length) {
      currentPosition = this.sentences[start].getRange().start;
      currentOffset = this.sentences[start].getDocumentOffset();
    } else {
      currentPosition = this.sentences[this.sentences.length-1].getRange().end;
      currentOffset = this.sentences[this.sentences.length-1].getDocumentOffset() + this.sentences[this.sentences.length-1].getText().length;
    }

    const reparsed : Sentence[] = [];
    for(let idx = 0; /**/; ++idx) {
      const parseText = this.documentText.substring(currentOffset);
      const len = parser.parseSentenceLength(parseText);

      if(len <= 0) {
        // end of parsable sentences
        // treat the rest of the document as unparsed
        const removed = this.sentences.splice(start, this.sentences.length - start, ...reparsed)
        removed.forEach((sent) => sent.dispose());
        return {removed: removed, added: reparsed, endOfSentences: true};
      }
      else if(idx >= minCount && start+idx < this.sentences.length && currentOffset+len === this.sentences[start+idx].getDocumentEndOffset()) {
        // no need to parse further; keep remaining sentences
        const removed = this.sentences.splice(start, idx, ...reparsed)
        removed.forEach((sent) => sent.dispose());
        return {removed: removed, added: reparsed, endOfSentences: false};
      }

      const command = parseText.substring(0, len);
      const range = Range.create(currentPosition, textUtil.positionAtRelative(currentPosition, command, len));
      reparsed.push(new Sentence(command, range, currentOffset));
      currentPosition = range.end;
      currentOffset+= len;
    }

  }

}
