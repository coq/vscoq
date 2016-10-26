/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';


import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import * as proto from './protocol';
import * as textUtil from './text-util';
// import {RangeSet} from './RangeSet';

import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';

function toRange(range: {start: {line: number, character: number}, end: {line: number, character: number}}) {
  return new vscode.Range(range.start.line,range.start.character,range.end.line,range.end.character);
}


// export enum HighlightType {
//   Clear,  SyntaxError,  TacticFailure,  Parsing,  Processing, Incomplete, Complete, InProgress, Processed 
// }
const parsingTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    outlineWidth: '1px',
    outlineStyle: 'solid', 
    overviewRulerColor: 'lightblue', 
    overviewRulerLane: vscode.OverviewRulerLane.Right,
    light: {outlineColor: 'darkblue'},
    dark: {outlineColor: 'lightblue'},
  });
const processingTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    overviewRulerColor: 'blue', 
    overviewRulerLane: vscode.OverviewRulerLane.Center,
    light: {backgroundColor: 'rgba(0,0,255,0.3)'},
    dark: {backgroundColor: 'rgba(0,0,255,0.3)'},
  });
const stateErrorTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    borderWidth: '1px',
    borderStyle: 'solid', 
    light:
      { borderColor: 'rgba(255,0,0,0.5)'
      , backgroundColor: 'rgba(255,0,0,0.25)'
      },
    dark:
      {borderColor: 'rgba(255,0,0,0.5)'
      , backgroundColor: 'rgba(255,0,0,0.25)'
      },
  });

const processedTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    overviewRulerColor: 'green', 
    overviewRulerLane: vscode.OverviewRulerLane.Center,
    light: {backgroundColor: 'rgba(0,150,0,0.2)'},
    dark: {backgroundColor: 'rgba(0,150,0,0.2)'},
  });
// Example: a Qed. whose proof failed.
const incompleteTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    overviewRulerColor: 'yellow',
    overviewRulerLane: vscode.OverviewRulerLane.Center,
    light: {backgroundColor: 'rgba(255,255,0,0.2)'},
    dark: {backgroundColor: 'rgba(255,255,0,0.2)'},
  });
const completeTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    overviewRulerColor: 'green', 
    overviewRulerLane: vscode.OverviewRulerLane.Center,
    light: {backgroundColor: 'rgba(0,255,255,0.2)'},
    dark: {backgroundColor: 'rgba(0,255,255,0.2)'},
  });
const inProgressTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    overviewRulerColor: 'purple', 
    overviewRulerLane: vscode.OverviewRulerLane.Center,
    light: {backgroundColor: 'lightpurple'},
    dark: {backgroundColor: 'darkpurple'},
  });


export class Highlights {
  // private textHighlights : {decoration: vscode.TextEditorDecorationType, ranges: RangeSet}[] = [];
  // private textHighlights : vscode.TextEditorDecorationType[];
  private current : {ranges: [ vscode.Range[], vscode.Range[], vscode.Range[], vscode.Range[], vscode.Range[], vscode.Range[], vscode.Range[] ]}
    = { ranges: [ [], [], [], [], [], [], [] ] };

  constructor() {
    // this.textHighlights[proto.HighlightType.Parsing   ] = parsingTextDecoration;
    // this.textHighlights[proto.HighlightType.Processing] = processingTextDecoration;
    // this.textHighlights[proto.HighlightType.StateError] = stateErrorTextDecoration;
    // this.textHighlights[proto.HighlightType.Processed ] = processedTextDecoration;
    // this.textHighlights[proto.HighlightType.Incomplete] = incompleteTextDecoration;
    // this.textHighlights[proto.HighlightType.Complete  ] = completeTextDecoration;
    // this.textHighlights[proto.HighlightType.InProgress] = inProgressTextDecoration;
  }

  public set(editors: Iterable<TextEditor>, highlights: proto.Highlights) {
    this.current = { ranges:
       [ highlights.ranges[0].map(toRange)
       , highlights.ranges[1].map(toRange)
       , highlights.ranges[2].map(toRange)
       , highlights.ranges[3].map(toRange)
       , highlights.ranges[4].map(toRange)
       , highlights.ranges[5].map(toRange)
       , highlights.ranges[6].map(toRange)
       ]};
    this.applyCurrent(editors);
  }

  public clearAll(editors: Iterable<TextEditor>) {
    this.current = { ranges: [ [], [], [], [], [], [], [] ] };
    this.applyCurrent(editors);
  }

  public refresh(editors: Iterable<TextEditor>) {
    this.applyCurrent(editors);
  }

  private applyCurrent(editors: Iterable<TextEditor>) {
    for(let editor of editors) {
      editor.setDecorations(stateErrorTextDecoration , this.current.ranges[proto.HighlightType.StateError]);
      editor.setDecorations(parsingTextDecoration    , this.current.ranges[proto.HighlightType.Parsing]);
      editor.setDecorations(processingTextDecoration , this.current.ranges[proto.HighlightType.Processing]);
      editor.setDecorations(incompleteTextDecoration , this.current.ranges[proto.HighlightType.Incomplete]);
      editor.setDecorations(completeTextDecoration   , this.current.ranges[proto.HighlightType.Complete]);
      editor.setDecorations(inProgressTextDecoration , this.current.ranges[proto.HighlightType.InProgress]);
      editor.setDecorations(processedTextDecoration  , this.current.ranges[proto.HighlightType.Processed]); 
    }
  }

  // public updateHighlights(editors: TextEditor[], params: proto.Highlights) {
  //   if(editors.length <= 0 || !editors[0])
  //     return;
  //   const anEditor = editors[0];

  //   for(const highlight of params.highlights) {
  //     const range = new vscode.Range(highlight.range.start.line,highlight.range.start.character,highlight.range.end.line,highlight.range.end.character);
  //     switch(highlight.style) {
  //       case proto.HighlightType.Clear:
  //         editors.forEach((editor) => this.clearHighlight(editor, range));
  //         break;
  //       case proto.HighlightType.SyntaxError:
  //       case proto.HighlightType.TacticFailure:
  //       default:
  //         editors.forEach((editor) => this.applyHighlight(editor, highlight.style, range));
  //     }
  //   }
  // }
  
  // public refreshHighlights(editors: vscode.TextEditor[]) {
  //   this.textHighlights
  //     .forEach((highlight,idx,a) => {
  //       editors.forEach((editor) =>
  //         editor.setDecorations(highlight.decoration,highlight.ranges.getRanges()));
  //     });
  // }

  // private applyHighlight(editor: vscode.TextEditor, type: proto.HighlightType, range: vscode.Range) {
  //   this.textHighlights
  //     .forEach((highlight,idx,a) => {
  //       if (idx!=type)
  //         highlight.ranges.subtract(range);
  //       else
  //         highlight.ranges.add(range);
  //       editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
  //     });
  // }

  // public clearAllHighlights(editors: vscode.TextEditor[]) {
  //   this.textHighlights
  //     .forEach((highlight,idx,a) => {
  //       highlight.ranges.clear();
  //       editors.forEach((editor) =>
  //         editor.setDecorations(highlight.decoration,highlight.ranges.getRanges()));
  //     });
  // }

  // private clearHighlight(editor: vscode.TextEditor, range: vscode.Range) {
  //   this.textHighlights
  //     .forEach((highlight,idx,a) => {
  //       highlight.ranges.subtract(range);
  //       editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
  //     });
  // }

  // public applyEdit(delta: textUtil.RangeDelta) {
  //   this.textHighlights
  //     .forEach((highlight) => {
  //       highlight.ranges.applyEdit(delta);
  //     });
  // }
// 
//   // Increases or decreases the number of characters in the highlight ranges starting
//   // at `position` and adjusts all subsequent ranges
//   public shiftCharacters(position: number, count: number) : boolean {
//     if(count == 0)
//       return;
//     const beginIdx = this.positionalIndexAt(position);
//     const beginSent = this.sentencesByPosition[beginIdx];
//     if(beginSent.textEnd > position) {
//       // contains the position
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

  // public toHighlightStrings() {
  //   return this.textHighlights
  //     .reduce((x,highlight,idx) => {
  //       var r = highlight.ranges.getRanges();
  //       if(r.length > 0)
  //         x[proto.HighlightType[idx]] = highlight.ranges.getRanges().map((r)=>r.toString()).join(',');
  //       return x}, {})
  // }

  // public toString() : string {
  //   return this.toHighlightStrings().toString();
  // }

}

