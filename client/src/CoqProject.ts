'use strict';

import * as vscode from 'vscode'
import * as proto from './protocol'
import {CoqDocument} from './CoqDocument'
export {CoqDocument} from './CoqDocument'
import {CoqLanguageServer} from './CoqLanguageServer'
import * as editorAssist from './EditorAssist'

export function getProject() : CoqProject {
  const coq = CoqProject.getInstance();
  if(!coq)
    throw "CoqProject not yet loaded";
  else
    return coq;
}

export class CoqProject implements vscode.Disposable {
  private documents = new Map<string, CoqDocument>();
  private activeEditor : vscode.TextEditor|null = null;
  /** the coq-doc that is either active, was the last to be active, or is associated with a helper view (proof-view) */
  private activeDoc : CoqDocument|null = null;
  private static instance : CoqProject|null = null;
  private langServer : CoqLanguageServer;
  private currentSettings: proto.CoqSettings;
  private subscriptions : vscode.Disposable[] = [];

  private constructor(context: vscode.ExtensionContext) {
    this.langServer = CoqLanguageServer.create(context);

    this.activeEditor = vscode.window.activeTextEditor;

    this.loadConfiguration();
    this.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e) => {
      editorAssist.reload();
      this.loadConfiguration();
    }));


    vscode.workspace.onDidChangeTextDocument((params) => this.onDidChangeTextDocument(params));
    vscode.workspace.onDidOpenTextDocument((params) => this.onDidOpenTextDocument(params));
    vscode.workspace.onDidCloseTextDocument((params) => this.onDidCloseTextDocument(params));
    vscode.window.onDidChangeActiveTextEditor((params) => this.onDidChangeActiveTextEditor(params));
    // Handle already-loaded documents
    vscode.workspace.textDocuments
      .forEach((textDoc) => this.tryLoadDocument(textDoc));

  }

  private loadConfiguration() {
    let conf = vscode.workspace.getConfiguration("coq") as vscode.WorkspaceConfiguration & proto.CoqSettings;
    if(conf.moveCursorToFocus === undefined)
      conf.moveCursorToFocus = true;
    this.currentSettings = conf;
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
    this.subscriptions.forEach((s) => s.dispose());
    this.langServer.dispose();
    this.subscriptions = [];
    this.documents.clear();
  }

  public get(uri: string): CoqDocument|null {
    return this.documents.get(uri) || null;
  }

  public getOrCurrent(uri: string): CoqDocument|null {
    return this.documents.get(uri) || this.activeDoc;
  }

  public getLanguageServer() : CoqLanguageServer {
    return this.langServer;
  }

  public get settings() : proto.CoqSettings {
    return this.currentSettings;
  }

  private tryLoadDocument(textDoc: vscode.TextDocument) {
    if(textDoc.languageId !== 'coq')
      return;
    const uri = textDoc.uri.toString();
    if(!this.documents.has(uri)) {
      this.documents.set(uri, new CoqDocument(textDoc, this));
    }

    // refresh this in case the loaded document has focus and it was not in our registry
    if(this.documents.has(vscode.window.activeTextEditor.document.uri.toString()))
      this.activeDoc = this.documents.get(vscode.window.activeTextEditor.document.uri.toString()) || null;
  }

  private onDidChangeTextDocument(params: vscode.TextDocumentChangeEvent) {
    const uri = params.document.uri.toString();
    const doc = this.documents.get(uri);
    if(!doc)
      return;
    doc.onDidChangeTextDocument(params);
// FOR DEBUGGING ONLY!!!
// doc.highlights.refresh(doc.allEditors());
  }

  private onDidOpenTextDocument(doc: vscode.TextDocument) {
    this.tryLoadDocument(doc);
  }

  private onDidCloseTextDocument(doc: vscode.TextDocument) {
    const uri = doc.uri.toString();
    const coqDoc = this.documents.get(uri);
    this.documents.delete(uri);
    if(!coqDoc)
      return;
    coqDoc.dispose();
  }

  public getActiveDoc() : CoqDocument|null {
    return this.activeDoc;
  }

  public setActiveDoc(doc: vscode.Uri|string) : void {
    this.activeDoc = this.documents.get(doc.toString()) || null;
  }

  private onDidChangeActiveTextEditor(editor: vscode.TextEditor) {
    if(!this.activeEditor)
      return;
    let oldUri : string|null;
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
    if(!uri) {
      if(oldDoc)
        oldDoc.doOnLostFocus();
    } else {
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
    }
    this.activeEditor = editor;
  }

  private async tryDocumentCommand(command: (editor: vscode.TextEditor) => Promise<void>, useActive=true, makeVisible = true, ...args: any[]) {
    let editor : vscode.TextEditor|null = vscode.window.activeTextEditor || null;
    let doc : CoqDocument | null;
    try {
      doc = editor ? this.documents.get(editor.document.uri.toString()) || null : null;
    } catch(err) {
      return;
    }

    if(!doc && useActive) {
      doc = this.activeDoc;
      editor = this.activeEditor;
    }

    if(doc) {
      let doc_ = doc; // TypeScript bug: does not realize the doc is not null in the next line, but this seems to work
      if(makeVisible && !vscode.window.visibleTextEditors.some((d) => d.document===doc_.getDocument()))
        await vscode.window.showTextDocument(doc.getDocument(), undefined, true);

      await command.call(doc,editor, ...args);
    }
  }

  public quitCoq() {
    return this.tryDocumentCommand(CoqDocument.prototype.quitCoq,false,false);
  }

  public resetCoq() {
    return this.tryDocumentCommand(CoqDocument.prototype.resetCoq,false,false);
  }

  public stepForward() {
    return this.tryDocumentCommand(CoqDocument.prototype.stepForward);
  }

  public stepBackward() {
    return this.tryDocumentCommand(CoqDocument.prototype.stepBackward);
  }

  public interpretToPoint(options : {synchronous?: boolean} = {}) {
    return this.tryDocumentCommand(CoqDocument.prototype.interpretToCursorPosition,false,false,options.synchronous);
  }

  public interpretToEnd(options : {synchronous?: boolean} = {}) {
    return this.tryDocumentCommand(CoqDocument.prototype.interpretToEnd,false,false,options.synchronous);
  }

  public interruptCoq() {
    return this.tryDocumentCommand(CoqDocument.prototype.interruptCoq);
  }

  public finishComputations() {
    return this.tryDocumentCommand(CoqDocument.prototype.finishComputations);
  }

  public ltacProfGetResults() {
    return this.tryDocumentCommand(CoqDocument.prototype.ltacProfGetResults);
  }

  public setCursorToFocus() {
    function helper(this: CoqDocument, editor: vscode.TextEditor) {
      return Promise.resolve(this.setCursorToFocus(editor,true,true));
    }
    return this.tryDocumentCommand(helper,false,false);
  }

  public setDisplayOption(item?: proto.DisplayOption, value?: proto.SetDisplayOption) {
    function setDisplayOption(this: CoqDocument, editor: vscode.TextEditor) {
      return Promise.resolve(this.setDisplayOption(item, value));
    }
    return this.tryDocumentCommand(setDisplayOption,true,false);
  }
}