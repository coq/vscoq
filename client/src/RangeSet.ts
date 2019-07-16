'use strict';

import * as vscode from 'vscode';
import * as textUtil from './text-util';

export class RangeSet {
  // sorted by start position; assume none overlap or touch
  private ranges: vscode.Range[] = [];
  
  public clear() : void {
    this.ranges = [];
  }
  
  
  public add(range: vscode.Range) {
    if(range.isEmpty)
      return;
    if(this.ranges.length == 0) {// init
      this.ranges.push(range);
      return;
    }

    // find the first intersecting range
    const beginPos = this.ranges.findIndex((r) => r.end.isAfterOrEqual(range.start));
    
    if(beginPos == -1) {// after pos
      this.ranges.push(range);
      return;
    }
    
    const r0 = this.ranges[beginPos];

    if(r0.start.isAfter(range.end)) {
      // insert before pos
      this.ranges.splice(beginPos,0,range);
      return;      
    }
    
    // find the range *just after* the last intersecting range
    let endPos = this.ranges.findIndex((r) => r.start.isAfter(range.end));
    // assume beginPos <= endPos (because this.ranges is sorted)

    if(endPos == -1)
      endPos = this.ranges.length;
      
    const r1 = this.ranges[endPos-1];
    this.ranges[beginPos] = r0.union(r1.union(range));
    this.ranges.splice(beginPos+1,endPos-beginPos-1);
  }
  
  public subtract(range: vscode.Range) {
    if(this.ranges.length == 0 || this.ranges[0].isEmpty || range.isEmpty) {
      return; // no intersection
    }

    // find the first intersecting range
    const beginPos = this.ranges.findIndex((r) => r.end.isAfter(range.start));
    
    if(beginPos == -1)
      return; // after pos; no intersection

    const r0a = this.ranges[beginPos].start;
    let remainder1 : vscode.Range;
    if(r0a.isAfterOrEqual(range.end))
      return; // no intersection
    else if(r0a.isAfterOrEqual(range.start))
      remainder1 = new vscode.Range(r0a, r0a);
    else
      remainder1 = new vscode.Range(r0a, range.start);
      
    // find the range *just after* the last intersecting range
    let endPos = this.ranges.findIndex((r) => r.end.isAfter(range.end));
    // assume beginPos <= endPos (because this.ranges is sorted)

    let remainder2 : vscode.Range;
    if(endPos == -1) {
      endPos = this.ranges.length;
      remainder2 = new vscode.Range(r0a,r0a); // empty range
    } else if(this.ranges[endPos].start.isAfterOrEqual(range.end))
      remainder2 = new vscode.Range(r0a,r0a);
    else {
      remainder2 = new vscode.Range(range.end, this.ranges[endPos].end);
      ++endPos; // endPos needs to be spliced below
    }

    if(remainder1.isEmpty) {
      if(remainder2.isEmpty) // remove full overlap
        this.ranges.splice(beginPos,endPos-beginPos);
      else {// part of r1 remains
        this.ranges.splice(beginPos,endPos-beginPos,remainder2);
      }
    } else if(remainder2.isEmpty) // part of r0a remains
      this.ranges.splice(beginPos,endPos-beginPos,remainder1);
    else
      this.ranges.splice(beginPos,endPos-beginPos,remainder1,remainder2);
  }


  public applyEdit(delta: textUtil.RangeDelta) {
    for(let idx = 0; idx < this.ranges.length; ++idx)
      this.ranges[idx] = textUtil.rangeTranslate(this.ranges[idx], delta);  
  }

  public toString() {
    return this.ranges.toString();
  }


  /**
   * case:  [A] X [B]  --> A
   * case:  [A-X] [B]  --> A
   * @returns the index of the range at or before the position, or -1 if no such range exists
   */
  // private indexAt(position: vscode.Position, begin?: number, end?: number) : number {
  //   // binary search!
  //   if(!begin)
  //     begin = 0;
  //   if(!end)
  //     end = this.ranges.length;
  //   while (begin < end) {
  //     const pivot = (begin + end) >> 1;
  //     const pivotRange = this.ranges[pivot];
  //     if(position.isBefore(pivotRange.start))
  //       end = pivot;
  //     else if(position.isBefore(pivotRange.end))
  //       return pivot;
  //     if (begin == pivot)
  //       break;
  //     else
  //       begin = pivot;
  //   }
  //   return begin;
  // }
// 
//   public insertShift(position: vscode.Position, linesDelta: number, charactersDelta: number) : boolean {
//     if(linesDelta == 0 && charactersDelta == 0)
//       return;
//     if(linesDelta < 0 || charactersDelta < 0)
//       return;
//     const beginIdx = this.indexAt(position);
//     const beginSent = this.ranges[beginIdx];
//     if(beginSent.end.isAfter(position) {
//       // contains the position
// 
//       beginSent.end.translate(linesDelta).with(undefined,charactersDelta);
//     } else if(beginIdx < this.sentencesByPosition.length-1
//       && -count > this.sentencesByPosition[beginIdx+1].textBegin-beginSent.textEnd) {
//       return false; // cannot remove more characters than exist between sentences      
//     }
//     
//     // shift subsequent sentences
//     for (let idx = beginIdx+1; idx < this.sentencesByPosition.length; ++idx) {
//       this.sentencesByPosition[idx].textBegin+= count;
//       this.sentencesByPosition[idx].textEnd+= count;
//     }
//     
//     return true;
//   }

  public getRanges() : vscode.Range[] {
    return this.ranges;
  }
}
// 
//   // Adds or removes from the range, starting at position and affecting all subsequent ranges
//   public shift(position: vscode.Position, linesDelta: number, charactersDelta: number) : boolean {
//     if(linesDelta == 0 && charactersDelta == 0)
//       return;
//     const beginIdx = this.indexAt(position);
//     const beginSent = this.ranges[beginIdx];
//     if(beginSent.end.isAfter(position) {
//       // contains the position
//       beginSent.end = tryTranslatePosition(beginSent.end, linesDelta, charactersDelta);
//       if(-count > beginSent.textEnd - beginSent.textBegin)
//         return false; // cannot remove more characters than a sentence has
//       beginSent.textEnd += count;
//     } else if(beginIdx < this.sentencesByPosition.length-1
//       && -count > this.sentencesByPosition[beginIdx+1].textBegin-beginSent.textEnd) {
//       return false; // cannot remove more characters than exist between sentences      
//     }
//     
//     // shift subsequent sentences
//     for (let idx = beginIdx+1; idx < this.sentencesByPosition.length; ++idx) {
//       this.sentencesByPosition[idx].textBegin+= count;
//       this.sentencesByPosition[idx].textEnd+= count;
//     }
//     
//     return true;
//   }


/*
) Starting ranges
[*****|***]   [****
*****]
1) insert on same line
[*****<++++++>***]   [****
*****]
2) insert with a line break
[*****<+++
+++>***]   [****
*****]

) Deleting on same line
[***<----->**]   [****
*****]
=
[*****]   [****
*****]

) Deleting on multiple lines
[***<--
----->**]   [****
*****]
=
[*****]   [****
*****]

*/
// 
// function shiftPosition(pos: vscode.Position, linesDelta: number, charactersDelta: number) : vscode.Position {
//   if(linesDelta > 1) {
//     return new vscode.Position(linesDelta,pos.character - );
//   }
//   if(linesDelta == 0 && ) {
//     
//   }
//   return null;
// }