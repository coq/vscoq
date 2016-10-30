'use strict';

import * as vscode from 'vscode'
import {CoqDocument} from './CoqDocument'
export {CoqDocument} from './CoqDocument'
import {CoqLanguageServer} from './CoqLanguageServer'
import * as util from 'util'

export function getProject() : CoqProject {
  if(!CoqProject.getInstance())
    throw "CoqProject not yet loaded";
  return CoqProject.getInstance();
}

export class CoqProject implements vscode.Disposable {
  private documents = new Map<string, CoqDocument>();
  private context: vscode.ExtensionContext;
  private activeEditor : vscode.TextEditor|null = null;
  /** the coq-doc that is either active, was the last to be active, or is associated with a helper view (proof-view) */
  private activeDoc : CoqDocument|null = null;
  private static instance : CoqProject|null = null;
  private langServer : CoqLanguageServer;

  private constructor(context: vscode.ExtensionContext) {
    this.context = context;
    this.langServer = CoqLanguageServer.create(context);

    this.activeEditor = vscode.window.activeTextEditor;

    vscode.workspace.onDidChangeTextDocument((params) => this.onDidChangeTextDocument(params));
    vscode.workspace.onDidOpenTextDocument((params) => this.onDidOpenTextDocument(params));
    vscode.workspace.onDidCloseTextDocument((params) => this.onDidOpenTextDocument(params));
    vscode.window.onDidChangeActiveTextEditor((params) => this.onDidChangeActiveTextEditor(params));
    // Handle already-loaded documents
    vscode.workspace.textDocuments
      .forEach((textDoc) => this.tryLoadDocument(textDoc));

    context.subscriptions.push(this);
  }

  public static create(context: vscode.ExtensionContext) {
    if(!CoqProject.instance)
      CoqProject.instance = new CoqProject(context);
    return CoqProject.instance;
  }

  public static getInstance() {
    return CoqProject.instance;
  }
  
  dispose() {
    this.documents.forEach((doc) => doc.dispose());
    this.langServer.dispose();
    this.documents.clear();
  }

  public get(uri: string): CoqDocument {
    return this.documents.get(uri);
  }

  public getOrCurrent(uri: string): CoqDocument {
    return this.documents.get(uri) || this.activeDoc;
  }

  public getLanguageServer() : CoqLanguageServer {
    return this.langServer;
  }

  private tryLoadDocument(textDoc: vscode.TextDocument) {
    if(textDoc.languageId !== 'coq')
      return;
    // console.log("try load coq doc: " + textDoc.uri.fsPath);
    const uri = textDoc.uri.toString();
    if(!this.documents.has(uri)) {
      this.documents.set(uri, new CoqDocument(textDoc.uri, this.context));
      // console.log("new coq doc: " + textDoc.uri.fsPath);
    }

    // refresh this in case the loaded document has focus and it was not in our registry
    if(this.documents.has(vscode.window.activeTextEditor.document.uri.toString()))
      this.activeDoc = this.documents.get(vscode.window.activeTextEditor.document.uri.toString());
  }

  private onDidChangeTextDocument(params: vscode.TextDocumentChangeEvent) {
    const uri = params.document.uri.toString();
    const editor = vscode.window.visibleTextEditors.find((editor, i, a) =>
      editor.document.uri.toString() === uri)
    const doc = this.documents.get(uri);
    if(!doc)
      return;
    doc.onDidChangeTextDocument(params);
// FOR DEBUGGING ONLY!!!
// doc.highlights.refresh(doc.allEditors());
  }

  private onDidOpenTextDocument(doc: vscode.TextDocument) {
    // console.log("opening: " + doc.uri.fsPath);
    this.tryLoadDocument(doc);
  }

  private onDidCloseTextDocument(doc: vscode.TextDocument) {
    const uri = doc.uri.toString();
    const coqDoc = this.documents.get(uri);
    if(!coqDoc)
      return;
    coqDoc.dispose();
    this.documents.delete(uri);
  }

  public getActiveDoc() : CoqDocument|null {
    return this.activeDoc;
  }

  public setActiveDoc(doc: vscode.Uri|string) : void {
    this.activeDoc = this.documents.get(doc.toString());
  }

  private onDidChangeActiveTextEditor(editor: vscode.TextEditor) {
    let oldUri : string;
    try {
      oldUri = this.activeEditor.document.uri.toString();
    } catch(err) {
      oldUri = null;
    }
    const oldDoc = oldUri ? this.documents.get(oldUri) : null;

    if(!editor) {
      if(oldDoc)
        oldDoc.doOnLostFocus();
      return;
    }

    // newly active editor
    const uri = editor.document ? editor.document.uri.toString() : null;
    const doc = this.documents.get(uri) || this.tryLoadDocument(editor.document);

    if(doc)
      this.activeDoc = doc;

    if(doc && oldDoc && uri==oldUri)
      doc.doOnSwitchActiveEditor(this.activeEditor, editor);
    else {
      if(doc)
        doc.doOnFocus(editor);
      if(oldDoc)
        oldDoc.doOnLostFocus();
    }

    this.activeEditor = editor;
 }

}