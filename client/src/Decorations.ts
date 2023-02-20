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

    const config = vscode.workspace.getConfiguration('vscoq.proof');

    decorations = {
        parsed: create({
            overviewRulerColor: 'cyan', 
            overviewRulerLane: vscode.OverviewRulerLane.Right,
        }),
        processing: create({
            overviewRulerColor: 'blue', 
            overviewRulerLane: vscode.OverviewRulerLane.Center,
        }),
        processed: create({
            overviewRulerColor: '#20b2aa', 
            overviewRulerLane: vscode.OverviewRulerLane.Left,
            light: {backgroundColor: 'rgba(0,150,0,0.2)'},
            dark: {backgroundColor: 'rgba(0,150,0,0.2)'},/* 
            light: config.checkMode === 0 ? {backgroundColor: 'rgba(0,150,0,0.2)'} : undefined,
            dark: config.checkMode === 0 ? {backgroundColor: 'rgba(0,150,0,0.2)'} : undefined, */
        }),
  };
}

