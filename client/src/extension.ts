'use strict';
import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';
import * as proto from './protocol';
import {CoqProject, CoqDocument} from './CoqProject';
import * as snippets from './Snippets';
const regenerate = require('regenerate');
import {initializeDecorations} from './Decorations';
import {HtmlCoqView} from './HtmlCoqView';

vscode.Range.prototype.toString = function rangeToString() {return `[${this.start.toString()},${this.end.toString()})`}
vscode.Position.prototype.toString = function positionToString() {return `{${this.line}@${this.character}}`}

console.log(`Coq Extension: process.version: ${process.version}, process.arch: ${process.arch}}`);

let project : CoqProject;

export var extensionContext : ExtensionContext;

// export function activate(context: ExtensionContext) {
//   const dec = vscode.window.createTextEditorDecorationType({
//     before: {contentText: "_$_", textDecoration: 'none; letter-spacing: normal; overflow: visible; font-size: 10em'},
//     textDecoration: 'none; font-size: 0.1em; letter-spacing: -0.55em; overflow: hidden; width: 0px; visibility: hidden',
//     // before: {contentText: "WORD", textDecoration: 'none; content: "WORD2"'},
//     // textDecoration: 'none; content: url(file:///C:/Users/cj/Research/vscoq/client/images/1x1.png)',
//     // textDecoration: 'none; position: absolute !important; top: -9999px !important; left: -9999px !important; letter-spacing: -1px',
//   });
//   function lineRange(line, start, end) { return new vscode.Range(line,start,line,end) }
//   const editor = vscode.window.activeTextEditor;
//   if (editor) {
//     const lines = [
//       "line1",
//       "small word: word",
//       "try selecting the previous line",
//       "END OF EXAMPLE", "", "", ]
//     editor.edit((edit) => {
//       edit.insert(new vscode.Position(0,0), lines.join('\n'));
//     }).then(() => {
//       editor.setDecorations(dec, [lineRange(1,12,16)]);
//     });
//   }  
// }

export function activate(context: ExtensionContext) {
  console.log(`execArgv: ${process.execArgv.join(' ')}`);
  console.log(`argv: ${process.argv.join(' ')}`);
  extensionContext = context;

  project = CoqProject.create(context);
  context.subscriptions.push(project);

  function regTCmd(command, callback) {
    context.subscriptions.push(vscode.commands.registerTextEditorCommand('extension.coq.'+command, callback));
  }
  function regCmd(command, callback, thisArg?: any) {
    context.subscriptions.push(vscode.commands.registerCommand('extension.coq.'+command, callback, thisArg));
  }
  function regProjectCmd(command, callback) {
    context.subscriptions.push(vscode.commands.registerCommand('extension.coq.'+command, callback, project));
  }

  initializeDecorations(context);

  regProjectCmd('quit', project.quitCoq);
  regProjectCmd('reset', project.resetCoq);
  regProjectCmd('interrupt', project.interruptCoq);
  regProjectCmd('stepForward', project.stepForward);
  regProjectCmd('stepBackward', project.stepBackward);
  regProjectCmd('interpretToPoint', project.interpretToPoint);
  regProjectCmd('interpretToPointSynchronous', () => project.interpretToPoint({synchronous: true}));
  regProjectCmd('interpretToEnd', project.interpretToEnd);
  regProjectCmd('interpretToEndSynchronous', () => project.interpretToEnd({synchronous: true}));
  regProjectCmd('moveCursorToFocus', project.setCursorToFocus);
  regTCmd('query.check', check);
  regTCmd('query.locate', locate);
  regTCmd('query.search', search);
  regTCmd('query.searchAbout', searchAbout); 
  regTCmd('query.print', print); 
  regTCmd('query.prompt.check', queryCheck);
  regTCmd('query.prompt.locate', queryLocate);
  regTCmd('query.prompt.search', querySearch);
  regTCmd('query.prompt.searchAbout', querySearchAbout); 
  regTCmd('query.prompt.print', queryPrint);
  regTCmd('proofView.open', viewGoalState); 
  regTCmd('proofView.openExternal', viewGoalStateExternal);
  regCmd('proofView.customizeProofViewStyle', customizeProofViewStyle);
  regProjectCmd('ltacProf.getResults', project.ltacProfGetResults);
  regCmd('display.toggle.implicitArguments', () => project.setDisplayOption(proto.DisplayOption.ImplicitArguments, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.coercions', () => project.setDisplayOption(proto.DisplayOption.Coercions, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.rawMatchingExpressions', () => project.setDisplayOption(proto.DisplayOption.RawMatchingExpressions, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.notations', () => project.setDisplayOption(proto.DisplayOption.Notations, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.allBasicLowLevelContents', () => project.setDisplayOption(proto.DisplayOption.AllBasicLowLevelContents, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.existentialVariableInstances', () => project.setDisplayOption(proto.DisplayOption.ExistentialVariableInstances, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.universeLevels', () => project.setDisplayOption(proto.DisplayOption.UniverseLevels, proto.SetDisplayOption.Toggle)); 
  regCmd('display.toggle.allLowLevelContents', () => project.setDisplayOption(proto.DisplayOption.AllLowLevelContents, proto.SetDisplayOption.Toggle));
  regCmd('display.toggle', () => project.setDisplayOption());

  vscode.languages.setLanguageConfiguration('coq', {
    indentationRules: {increaseIndentPattern: /^\s*(?:\bProof\b|\*|\+|\-)/, decreaseIndentPattern: /^\s*(?:\bQed\b)/},
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
  })

  snippets.setupSnippets(context.subscriptions);
}

async function withDocAsync<T>(editor: TextEditor, callback: (doc: CoqDocument) => Promise<T>) : Promise<void> {
  const doc = project.getOrCurrent(editor ? editor.document.uri.toString() : null);
  if(doc)
    await callback(doc);
}


async function queryStringFromPlaceholder(prompt: string, editor: TextEditor) {
  let placeHolder = editor.document.getText(editor.selection);
  if(editor.selection.isEmpty)
    placeHolder = editor.document.getText(editor.document.getWordRangeAtPosition(editor.selection.active));
  return await vscode.window.showInputBox({
    prompt: prompt,
    value: placeHolder
    });
}

async function queryStringFromPosition(prompt: string, editor: TextEditor) {
  let query = editor.document.getText(editor.selection);
  if(editor.selection.isEmpty)
    query = editor.document.getText(editor.document.getWordRangeAtPosition(editor.selection.active));
  if(query.trim() === "")
    return await queryStringFromPlaceholder(prompt, editor);
  else
    return query;
}

function queryCheck(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.check(await queryStringFromPlaceholder("Check:", editor))
  )
}

function queryLocate(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.locate(await queryStringFromPlaceholder("Locate:", editor))
  )
}

function querySearch(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.search(await queryStringFromPlaceholder("Search:", editor))
  )
}

function querySearchAbout(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.searchAbout(await queryStringFromPlaceholder("Search About:", editor))
  )
}

function queryPrint(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.print(await queryStringFromPlaceholder("Print:", editor))
  )
}

function check(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.check(await queryStringFromPosition("Check:", editor))
  )
}

function locate(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.locate(await queryStringFromPosition("Locate:", editor))
  )
}

function search(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.search(await queryStringFromPosition("Search:", editor))
  )
}

function searchAbout(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.searchAbout(await queryStringFromPosition("Search About:", editor))
  )
}

function print(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.print(await queryStringFromPosition("Search About:", editor))
  )
}

function viewGoalState(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.viewGoalState(editor,false)
  )
}

function viewGoalStateExternal(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.viewGoalState(editor,true)
  )
}

function customizeProofViewStyle() {
  HtmlCoqView.customizeProofViewStyle();
}