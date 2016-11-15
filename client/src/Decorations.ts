'use strict';


import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import * as proto from './protocol';
import * as textUtil from './text-util';
// import {RangeSet} from './RangeSet';

import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';

const STM_FOCUS_IMAGE = "./images/stm-focus.svg";
const STM_FOCUS_IMAGE_BEFORE = "./images/stm-focus-before.svg";

interface Decorations {
  readonly parsing: vscode.TextEditorDecorationType;
  readonly processing: vscode.TextEditorDecorationType;
  readonly stateError: vscode.TextEditorDecorationType;
  readonly processed: vscode.TextEditorDecorationType
  readonly incomplete: vscode.TextEditorDecorationType; // Example: a Qed. whose proof failed.
  readonly axiom: vscode.TextEditorDecorationType;
  readonly focus : vscode.TextEditorDecorationType;
  readonly focusBefore : vscode.TextEditorDecorationType;
}

interface DecorationsInternal extends Decorations {
  parsing: vscode.TextEditorDecorationType;
  processing: vscode.TextEditorDecorationType;
  stateError: vscode.TextEditorDecorationType;
  processed: vscode.TextEditorDecorationType
  incomplete: vscode.TextEditorDecorationType; // Example: a Qed. whose proof failed.
  axiom: vscode.TextEditorDecorationType;
  focus : vscode.TextEditorDecorationType;
  focusBefore : vscode.TextEditorDecorationType;
}


export let decorations : Decorations;
let decorationsInteral : DecorationsInternal;

export function initializeDecorations(context: vscode.ExtensionContext) {
  function create(style : vscode.DecorationRenderOptions) {
    const result = vscode.window.createTextEditorDecorationType(style);
    context.subscriptions.push(result);
    return result;
  }
  decorationsInteral = {
    parsing: create({
      outlineWidth: '1px',
      outlineStyle: 'solid', 
      overviewRulerColor: 'cyan', 
      overviewRulerLane: vscode.OverviewRulerLane.Right,
      light: {outlineColor: 'rgba(32, 165, 218,0.7)', backgroundColor: 'rgba(0, 255, 255, 0.2)'},
      dark: {outlineColor: 'rgba(32, 165, 218,0.7)', backgroundColor: 'rgba(0, 255, 255, 0.2)'},
    }),
    processing: create({
      overviewRulerColor: 'blue', 
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'rgba(0,0,255,0.3)'},
      dark: {backgroundColor: 'rgba(0,0,255,0.3)'},
    }),
    stateError: create({
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
    }),
    processed: create({
      overviewRulerColor: 'green', 
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'rgba(0,150,0,0.2)'},
      dark: {backgroundColor: 'rgba(0,150,0,0.2)'},
    }),
    axiom: create({
      overviewRulerColor: 'yellow',
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'rgba(255,255,0,0.2)'},
      dark: {backgroundColor: 'rgba(255,255,0,0.2)'},
    }),
    incomplete: create({
      overviewRulerColor: 'purple', 
      overviewRulerLane: vscode.OverviewRulerLane.Center,
      light: {backgroundColor: 'lightpurple'},
      dark: {backgroundColor: 'darkpurple'},
    }),
    focus: create({
      gutterIconPath: context.asAbsolutePath(STM_FOCUS_IMAGE),
      gutterIconSize: "contain"
    }),
    focusBefore: create({
      gutterIconPath: context.asAbsolutePath(STM_FOCUS_IMAGE_BEFORE),
      gutterIconSize: "contain"
    })
  };

  decorations = decorationsInteral;
}

