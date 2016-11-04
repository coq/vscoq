'use strict';
import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';
import * as proto from './protocol';
import {CoqProject, CoqDocument} from './CoqProject';


vscode.Range.prototype.toString = function rangeToString() {return `[${this.start.toString()},${this.end.toString()})`}
vscode.Position.prototype.toString = function positionToString() {return `{${this.line}@${this.character}}`}

console.log(`Coq Extension: process.version: ${process.version}, process.arch: ${process.arch}}`);

// from 'vscode-languageserver'
// export interface TextDocumentIdentifier {
//     uri: string;
// } 

let project : CoqProject;

export var extensionContext : ExtensionContext;


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

  regProjectCmd('quit', project.quitCoq);
  regProjectCmd('reset', project.resetCoq);
  regProjectCmd('interrupt', project.interruptCoq);
  regProjectCmd('stepForward', project.stepForward);
  regProjectCmd('stepBackward', project.stepBackward);
  regProjectCmd('interpretToPoint', project.interpretToPoint);
  regProjectCmd('interpretToEnd', project.interpretToEnd);
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


  function snippetSentence(text: string) : vscode.CompletionItem{
    const result = new vscode.CompletionItem(text,vscode.CompletionItemKind.Snippet);
    result.insertText = text + ".";
    return result;
  }
  vscode.languages.registerCompletionItemProvider('coq', {
    provideCompletionItems: (doc, pos, token) : vscode.CompletionItem[] => {
      return [
        "Set Asymmetric Patterns",
        "Set Atomic Load",
        "Set Automatic Coercions Import",
        "Set Automatic Introduction",
        "Set Boolean Equality Schemes",
        "Set Bracketing Last Introduction Pattern",
        "Set Bullet Behavior",
        "Set Subproofs Case Analysis Schemes",
        "Set Compat Notations",
        "Set Congruence Depth",
        "Set Congruence Verbose",
        "Set Contextual Implicit",
        "Set Debug Auto",
        "Set Debug Eauto",
        "Set Debug Rakam",
        "Set Debug Tactic Unification",
        "Set Debug Trivial",
        "Set Debug Unification",
        "Set Decidable Equality Schemes",
        "Set Default Clearing Used Hypotheses",
        "Set Default Goal Selector",
        "Set Default Proof Mode",
        "Set Default Proof Using",
        "Set Default Timeout",
        "Set Dependent Propositions Elimination",
        "Set Discriminate Introduction",
        "Set Dump Bytecode",
        "Set Elimination Schemes",
        "Set Equality Scheme",
        "Set Extraction Auto Inline",
        "Set Extraction Conservative Types",
        "Set Extraction File Comment",
        "Set Extraction Flag",
        "Set Extraction Keep Singleton",
        "Set Extraction Optimize",
        "Set Extraction Safe Implicits",
        "Set Extraction Type Expand",
        "Set Firstorder Depth",
        "Set Hide Obligations",
        "Set Implicit Arguments",
        "Set Info Auto",
        "Set Info Eauto",
        "Set Info Level",
        "Set Info Trivial",
        "Set Injection L2 Rpattern Order",
        "Set Injection On Proofs",
        "Set Inline Level",
        "Set Intuition Iff Unfolding",
        "Set Intuition Negation Unfolding",
        "Set Kernel Term Sharing",
        "Set Keyed Unification",
        "Set Loose Hint Behavior",
        "Set Maximal Implicit Insertion",
        "Set Nonrecursive Elimination Schemes",
        "Set Parsing Explicit",
        "Set Primitive Projections",
        "Set Printing All",
        "Set Printing Coercions",
        "Set Printing Depth",
        "Set Printing Existential Instances",
        "Set Printing Implicit",
        "Set Printing Implicit Defensive",
        "Set Printing Matching",
        "Set Printing Notations",
        "Set Printing Primitive Projection Compatibility",
        "Set Printing Primitive Projection Parameters",
        "Set Printing Projections",
        "Set Printing Records",
        "Set Printing Synth",
        "Set Printing Universes",
        "Set Printing Width",
        "Set Printing Wildcard",
        "Set Program Mode",
        "Set Proof Using Clear Unused",
        "Set Record Elimination Schemes",
        "Set Regular Subst Tactic",
        "Set Reversible Pattern Implicit",
        "Set Rewriting Schemes",
        "Set Short Module Printing",
        "Set Shrink Obligations",
        "Set Simpl Is Cbn",
        "Set Standard Proposition Elimination Names",
        "Set Strict Implicit",
        "Set Strict Proofs",
        "Set Strict Universe Declaration",
        "Set Strongly Strict Implicit",
        "Set Suggest Proof Using",
        "Set Tactic Compat Context",
        "Set Tactic Evars Pattern Unification",
        "Set Transparent Obligations",
        "Set Typeclass Resolution After Apply",
        "Set Typeclass Resolution For Conversion",
        "Set Typeclasses Debug",
        "Set Typeclasses Dependency Order",
        "Set Typeclasses Depth",
        "Set Typeclasses Modulo Eta",
        "Set Typeclasses Strict Resolution",
        "Set Typeclasses Unique Instances",
        "Set Typeclasses Unique Solutions",
        "Set Universal Lemma Under Conjunction",
        "Set Universe Minimization To Set",
        "Set Universe Polymorphism",
        "Set Verbose Compat Notations" ]
        .map(snippetSentence);
    }});
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
