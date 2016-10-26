'use strict';
import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';
import * as proto from './protocol';
import {CoqDocumentListener, CoqDocument} from './CoqDocumentListener';


vscode.Range.prototype.toString = function rangeToString() {return `[${this.start.toString()},${this.end.toString()})`}
vscode.Position.prototype.toString = function positionToString() {return `{${this.line}@${this.character}}`}

console.log(`Coq Extension: process.version: ${process.version}, process.arch: ${process.arch}}`);

// from 'vscode-languageserver'
// export interface TextDocumentIdentifier {
//     uri: string;
// } 

let documents : CoqDocumentListener;

export var extensionContext : ExtensionContext;

export function activate(context: ExtensionContext) {
  extensionContext = context;
  documents = new CoqDocumentListener(context);
  function regTCmd(command, callback) {
    context.subscriptions.push(vscode.commands.registerTextEditorCommand('extension.coq.'+command, callback));
  }

  regTCmd('quit', quitCoq);
  regTCmd('reset', resetCoq);
  regTCmd('interrupt', interruptCoq);
  regTCmd('stepForward', stepForward);
  regTCmd('stepBackward', stepBackward);
  regTCmd('interpretToPoint', interpretToPoint);
  regTCmd('interpretToEnd', interpretToEnd);
  regTCmd('check', check);
  regTCmd('locate', locate);
  regTCmd('search', search);
  regTCmd('searchAbout', searchAbout); 
  regTCmd('print', print); 
  regTCmd('queryCheck', queryCheck);
  regTCmd('queryLocate', queryLocate);
  regTCmd('querySearch', querySearch);
  regTCmd('querySearchAbout', querySearchAbout); 
  regTCmd('queryPrint', queryPrint);
  regTCmd('viewGoalState', viewGoalState); 
  regTCmd('viewGoalStateExternal', viewGoalStateExternal);
  regTCmd('ltacProfGetResults', ltacProfGetResults);
  regTCmd('toggleDisplayImplicitArguments', (t,e) => setDisplayOption(t,e,proto.DisplayOption.ImplicitArguments, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayCoercions', (t,e) => setDisplayOption(t,e,proto.DisplayOption.Coercions, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayRawMatchingExpressions', (t,e) => setDisplayOption(t,e,proto.DisplayOption.RawMatchingExpressions, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayNotations', (t,e) => setDisplayOption(t,e,proto.DisplayOption.Notations, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayAllBasicLowLevelContents', (t,e) => setDisplayOption(t,e,proto.DisplayOption.AllBasicLowLevelContents, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayExistentialVariableInstances', (t,e) => setDisplayOption(t,e,proto.DisplayOption.ExistentialVariableInstances, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayUniverseLevels', (t,e) => setDisplayOption(t,e,proto.DisplayOption.UniverseLevels, proto.SetDisplayOption.Toggle)); 
  regTCmd('toggleDisplayAllLowLevelContents', (t,e) => setDisplayOption(t,e,proto.DisplayOption.AllLowLevelContents, proto.SetDisplayOption.Toggle));
  regTCmd('toggleDisplay', (t,e) => setDisplayOption(t,e));

  // vscode.languages.registerCompletionItemProvider('coq', {provideCompletionItems: provideOptionCompletions}, 'X');
}

// function provideOptionCompletions(document: vscode.TextDocument, position: vscode.Position, token: vscode.CancellationToken): vscode.CompletionItem[] {
//   const wordRange = document.lineAt(position.line);
//   if(!wordRange)
//     return [];
//   const wordAtPosition = document.getText();
//   const optionsMatch = /^[(.*)]$/.exec(wordAtPosition);
//   if(optionsMatch) {
//     const options = optionsMatch[1].split('|');
//     return options.map((o) => <vscode.CompletionItem>{label:o});
//   }
//   
// }

// function withDoc<T>(editor: TextEditor, callback: (doc: CoqDocument) => T) : void {
//   const doc = documents.get(editor.document.uri.toString());
//   if(doc)
//     callback(doc);
// }

async function withDocAsync<T>(editor: TextEditor, callback: (doc: CoqDocument) => Promise<T>) : Promise<void> {
  const doc = documents.get(editor.document.uri.toString());
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

function quitCoq(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.quitCoq(editor)
  )
}

function resetCoq(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.resetCoq(editor)
  )
}

function interruptCoq(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.interruptCoq()
  )
}

function stepForward(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.stepForward(editor)
  )
}

function stepBackward(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.stepBackward(editor)
  )
}

function interpretToPoint(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.interpretToCursorPosition(editor)
  )
}

function interpretToEnd(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.interpretToEnd(editor)
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

function ltacProfGetResults(editor: TextEditor, edit: TextEditorEdit) {
  return withDocAsync(editor, async (doc) =>
    doc.ltacProfGetResults(editor)
  )
}

function setDisplayOption(editor: TextEditor, edit: TextEditorEdit, item?: proto.DisplayOption, value?: proto.SetDisplayOption) : void {
  withDocAsync(editor, async (doc) =>
    doc.setDisplayOption(item, value)
  )
}

