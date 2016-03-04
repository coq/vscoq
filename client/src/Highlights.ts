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
import {RangeSet} from './RangeSet';

import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';


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
const syntaxErrorTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    gutterIconPath: "C:/Users/cj/vscode_coq/client/src/syntax_error_icon.svg"
    });
const tacticErrorTextDecoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
    outlineWidth: '1px',
    outlineStyle: 'solid', 
    light: {outlineColor: 'rgba(255,0,0,0.5)'},
    dark: {outlineColor: 'rgba(255,0,0,0.5)'},
    // light: {backgroundColor: 'lightred'},
    // dark: {backgroundColor: 'darkred'},
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
  private textHighlights : {decoration: vscode.TextEditorDecorationType, ranges: RangeSet}[] = [];

  constructor() {
    this.textHighlights[proto.HighlightType.Parsing] = {
      decoration: parsingTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.Processing] = {
      decoration: processingTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.TacticFailure] = {
      decoration: tacticErrorTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.Processed] = {
      decoration: processedTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.Incomplete] = {
      decoration: incompleteTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.Complete] = {
      decoration: completeTextDecoration,
      ranges: new RangeSet()
    }
    this.textHighlights[proto.HighlightType.InProgress] = {
      decoration: inProgressTextDecoration,
      ranges: new RangeSet()
    }
  }

  public updateHighlights(editor: TextEditor, params: proto.NotifyHighlightParams) {
    if(!editor)
      return;
    for(const highlight of params.highlights) {
      const range = new vscode.Range(editor.document.positionAt(highlight.textBegin),
        editor.document.positionAt(highlight.textEnd));
      switch(highlight.style) {
        case proto.HighlightType.Clear:
          this.clearHighlight(editor, range);  break;
        case proto.HighlightType.SyntaxError:
        case proto.HighlightType.TacticFailure:
        default:
          this.applyHighlight(editor, highlight.style, range)
      }
    }  
  }
  
  public refreshHighlights(editor: vscode.TextEditor) {
    this.textHighlights
      .forEach((highlight,idx,a) => {
        editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
      });
  }

  private applyHighlight(editor: vscode.TextEditor, type: proto.HighlightType, range: vscode.Range) {
    this.textHighlights
      .forEach((highlight,idx,a) => {
        if (idx!=type)
          highlight.ranges.subtract(range);
        else
          highlight.ranges.add(range);
        editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
      });
  }

  public clearAllHighlights(editor: vscode.TextEditor) {
    this.textHighlights
      .forEach((highlight,idx,a) => {
        highlight.ranges.clear();
        editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
      });
  }

  private clearHighlight(editor: vscode.TextEditor, range: vscode.Range) {
    this.textHighlights
      .forEach((highlight,idx,a) => {
        highlight.ranges.subtract(range);
        editor.setDecorations(highlight.decoration,highlight.ranges.getRanges());
      });
  }

  public applyEdit(delta: textUtil.RangeDelta) {
    this.textHighlights
      .forEach((highlight) => {
        highlight.ranges.applyEdit(delta);
      });
  }
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

  public toHighlightStrings() {
    return this.textHighlights
      .reduce((x,highlight,idx) => {
        var r = highlight.ranges.getRanges();
        if(r.length > 0)
          x[proto.HighlightType[idx]] = highlight.ranges.getRanges().map((r)=>r.toString()).join(',');
        return x}, {})
  }

  public toString() : string {
    return this.toHighlightStrings().toString();
  }

}

