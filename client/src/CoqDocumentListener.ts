'use strict';

import * as vscode from 'vscode'
import {CoqDocument} from './CoqDocument'

export class CoqDocumentListener implements vscode.Disposable {
  private documents = new Map<string, CoqDocument>();
  private context: vscode.ExtensionContext;
  private activeEditor : vscode.TextEditor = null;

  constructor(context: vscode.ExtensionContext) {
    this.context = context;

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
  
  dispose() {
    this.documents.forEach((doc) => doc.dispose());
  }

  public get(uri: string): CoqDocument {
    return this.documents.get(uri);
  }

  private tryLoadDocument(textDoc: vscode.TextDocument) {
    if(textDoc.languageId !== 'coq')
      return;
    const uri = textDoc.uri.toString();
    this.documents.set(uri, new CoqDocument(textDoc.uri, this.context));    
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
doc.highlights.refreshHighlights(doc.allEditors());
  }

  private onDidOpenTextDocument(doc: vscode.TextDocument) {
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

  private onDidChangeActiveTextEditor(editor: vscode.TextEditor) {
    const oldUri = this.activeEditor ? this.activeEditor.document.uri.toString() : null;
    const oldDoc = this.documents.get(oldUri);
    if(oldDoc)
      oldDoc.doOnLostFocus();

    this.activeEditor = vscode.window.activeTextEditor;

    const uri = editor.document.uri.toString();
    const doc = this.documents.get(uri);
    if(doc)
      doc.doOnFocus(editor);
 }

}