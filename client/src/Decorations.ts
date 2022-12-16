'use strict';
import * as vscode from 'vscode';

interface Decorations {
  parsed: vscode.TextEditorDecorationType;
  processing: vscode.TextEditorDecorationType;
  processed: vscode.TextEditorDecorationType
}

export let decorations : Decorations;

export function initializeDecorations(context: vscode.ExtensionContext) {
  function create(style : vscode.DecorationRenderOptions) {
    const result = vscode.window.createTextEditorDecorationType(style);
    context.subscriptions.push(result);
    return result;
  }
  decorations = {
    parsed: create({
      outlineWidth: '1px',
      outlineStyle: 'solid', 
      overviewRulerColor: 'cyan', 
      overviewRulerLane: vscode.OverviewRulerLane.Right,
      light: {outlineColor: 'rgba(32, 165, 218,0.7)', backgroundColor: 'red'},
      dark: {outlineColor: 'rgba(32, 165, 218,0.7)', backgroundColor: 'red'},
    }),
    processing: create({
      overviewRulerColor: 'blue', 
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'blue'},
      dark: {backgroundColor: 'blue'},
    }),
    processed: create({
      overviewRulerColor: 'green', 
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'green'},
      dark: {backgroundColor: 'green'},
    }),
  };
}

