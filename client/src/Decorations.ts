'use strict';
import * as vscode from 'vscode';
import { DidChangeConfigurationParams } from 'vscode-languageclient';

interface Decorations {
  prepared: vscode.TextEditorDecorationType;
  processing: vscode.TextEditorDecorationType;
  processed: vscode.TextEditorDecorationType
}

export let decorationsContinuous : Decorations;
export let decorationsManual : Decorations;
export let decorationsErrorAnimation : vscode.TextEditorDecorationType[];

export function initializeDecorations(context: vscode.ExtensionContext) {
  
    function create(style : vscode.DecorationRenderOptions) {
        const result = vscode.window.createTextEditorDecorationType(style);
        context.subscriptions.push(result);
        return result;
    }

    decorationsContinuous = {
        prepared: create({
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
        }),
    };

    decorationsManual = {
        prepared: create({
            outlineWidth: '1px',
            outlineStyle: 'solid', 
            overviewRulerColor: 'cyan', 
            overviewRulerLane: vscode.OverviewRulerLane.Right,
            light: {outlineColor: 'rgba(32, 165, 218,0.7)', backgroundColor: 'rgba(0, 255, 255, 0.2)'},
        }),
        processing: create({
            overviewRulerColor: 'blue', 
            overviewRulerLane: vscode.OverviewRulerLane.Center,
            light: {backgroundColor: 'rgba(0,0,255,0.3)'},
            dark: {backgroundColor: 'rgba(0,0,255,0.3)'},
        }),
        processed: create({
            overviewRulerColor: '#20b2aa', 
            overviewRulerLane: vscode.OverviewRulerLane.Left,
            light: {backgroundColor: 'rgba(0,150,0,0.2)'},
            dark: {backgroundColor: 'rgba(0,150,0,0.2)'},
        }),
    };

    const opacities = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9];
    const opacityRange = opacities.concat([1]).concat(opacities.reverse());


    decorationsErrorAnimation = opacityRange.map( opacity => {
        return create({
            dark: {
                backgroundColor: `rgba(150,0,0,${opacity})`,
            },
            light: {
                backgroundColor: `rgba(150,0,0,${opacity})`,
            }
        });
    });

}

