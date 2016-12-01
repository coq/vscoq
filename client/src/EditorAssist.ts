import * as vscode from 'vscode';
const regenerate = require('regenerate');
import {Settings, CoqSettings, CoqEditorSettings} from './protocol';

let subscriptions : vscode.Disposable[] = [];

export function unload() {
  subscriptions.forEach(x => x.dispose());
  subscriptions = [];
}

export function reload() : vscode.Disposable {
  unload();

  const settings = vscode.workspace.getConfiguration("coq") as any as CoqSettings;
  const bulletIndentation = settings.editor.indentAfterBullet;

  const increaseIndentPattern =
    bulletIndentation==="indent"
    ? /^\s*(?:\bProof\b|\*|\+|\-)/
    : /^\s*(?:\bProof\b)/;

  subscriptions.push(vscode.languages.setLanguageConfiguration('coq', {
    indentationRules: {increaseIndentPattern: increaseIndentPattern, decreaseIndentPattern: /^\s*(?:\bQed\b)/},
    wordPattern: new RegExp(
      "(?:" +
      regenerate()
      .add(require('unicode-9.0.0/General_Category/Lowercase_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Uppercase_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Other_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Titlecase_Letter/code-points'))
      .addRange(0x1D00, 0x1D7F) // Phonetic Extensions.
      .addRange(0x1D80, 0x1DBF) // Phonetic Extensions Suppl.
      .addRange(0x1DC0, 0x1DFF) // Combining Diacritical Marks Suppl.
      .add(0x005F)              // Underscore.
      .add(0x00A0)              // Non-breaking space.
      .toString()
      + ")" + "(?:" +
      regenerate()
      .add(require('unicode-9.0.0/General_Category/Lowercase_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Uppercase_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Other_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Titlecase_Letter/code-points'))
      .add(require('unicode-9.0.0/General_Category/Decimal_Number/code-points'))
      .add(require('unicode-9.0.0/General_Category/Letter_Number/code-points'))
      .add(require('unicode-9.0.0/General_Category/Other_Number/code-points'))
      .addRange(0x1D00, 0x1D7F) // Phonetic Extensions.
      .addRange(0x1D80, 0x1DBF) // Phonetic Extensions Suppl.
      .addRange(0x1DC0, 0x1DFF) // Combining Diacritical Marks Suppl.
      .add(0x005F)              // Underscore.
      .add(0x00A0)              // Non-breaking space.
      .add(0x0027)              // Special space/
      .toString()
      + ")*")
  }))

  return { dispose: () => unload() }
}