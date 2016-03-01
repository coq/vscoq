'use strict';

import * as vscode from 'vscode';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient } from 'vscode-languageclient';


import {Highlights} from './Highlights';
import {CoqView, SimpleCoqView} from './SimpleCoqView';
import {MDCoqView} from './MDCoqView';
import {HtmlCoqView} from './HtmlCoqView';
import * as proto from './protocol';
import * as textUtil from './text-util';
import {CoqLanguageServer} from './CoqLanguageServer';

export class CoqDocument implements vscode.Disposable {
  private statusBar: vscode.StatusBarItem;
  public documentUri: string;
  public highlights = new Highlights();
  private viewDoc: vscode.TextDocument = null;
  private langServer: CoqLanguageServer;
  private view : CoqView;
  private infoOut: vscode.OutputChannel;

  constructor(uri: vscode.Uri, context: ExtensionContext) {
    this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 1);
    this.statusBar.text = 'Loading Coq';
    this.statusBar.show();

    this.documentUri = uri.toString();
    this.langServer = new CoqLanguageServer(context);

    this.infoOut = vscode.window.createOutputChannel('Info');
    
    this.view = new HtmlCoqView(uri);
    // this.view = new SimpleCoqView(uri.toString());
    // this.view = new MDCoqView(uri);


    this.langServer.onUpdateHighlights((p) => this.onDidUpdateHighlights(p));
    this.langServer.onMessage((p) => this.onCoqMessage(p));
    this.langServer.onReset((p) => { if (p.uri == this.documentUri) this.onCoqReset(); });
    this.langServer.onUpdateStateViewUrl((p) => { if (p.uri == this.documentUri) this.updateStateViewUrl(p.stateUrl); });

    context.subscriptions.push(this.langServer.start());
    // const viewFile = this.documentUri + '.view.md';
    // vscode.workspace.openTextDocument(viewFile)
    //   .then((viewDoc) => {
    //     this.viewDoc = viewDoc;
    //     vscode.window.showTextDocument(viewDoc, vscode.ViewColumn.Three);
    //   });

    this.view.onresize = async (columns:number) => {
      await this.langServer.resizeView(this.documentUri,Math.floor(columns));
      const value = await this.langServer.getGoal(this.documentUri);
      this.view.update(value);
    };

  }
  
  private updateStateViewUrl(stateUrl: string) {
    // if(this.view)
    //   this.view.dispose();
    // this.view = new HttpCoqView(vscode.Uri.parse(this.documentUri), stateUrl);
  }


  public getUri() {
    return this.documentUri;
  }

  dispose() {
    this.statusBar.dispose();
    this.view.dispose();
  }

  private reset(editor: vscode.TextEditor) {
    this.highlights.clearAllHighlights(editor)
  }

  private onDidUpdateHighlights(params: proto.NotifyHighlightParams) {
    this.updateHighlights(this.findEditor(),params);
  }
  
  private onCoqMessage(params: proto.NotifyMessageParams) {
    switch(params.level) {
    case 'warning':
      vscode.window.showWarningMessage(params.message); return;
    case 'info':
      // this.infoOut.appendLine(params.message); return;
      // this.view.message(params.message);
      this.infoOut.append(params.message);
      return;
    case 'notice':
      this.infoOut.clear();
      this.infoOut.append(params.message);
      return;
      // vscode.window.showInformationMessage(params.message); return;
    case 'error':
      vscode.window.showErrorMessage(params.message); return;
    }
  }


  public onDidChangeTextDocument(params: vscode.TextDocumentChangeEvent) {
    for (const change of params.contentChanges) {
      const changeRange = textUtil.toRangeDelta(change.range, change.text);
      this.highlights.applyEdit(changeRange);
    }
  }

  public updateHighlights(editor : vscode.TextEditor, params: proto.NotifyHighlightParams) {
    this.highlights.updateHighlights(editor,params);
  }

  public interruptCoq() {
    this.langServer.interruptCoq(this.documentUri);
  }

  public async quitCoq(editor: TextEditor) {
    this.statusBar.text = 'Killing CoqTop';
    await this.langServer.quitCoq(this.documentUri);
    this.reset(editor);
  }

  public async resetCoq(editor: TextEditor) {
    this.statusBar.text = 'Resetting Coq';
    await this.langServer.resetCoq(this.documentUri);
    this.reset(editor);
  }
  
  private findEditor() : vscode.TextEditor {
    return vscode.window.visibleTextEditors.find((editor,i,a) => 
      editor.document.uri.toString() === this.documentUri)
  }
  
  private onCoqReset() {
    this.statusBar.text = 'Ready';
    this.reset(this.findEditor());
  }

  public async stepForward(editor: TextEditor) {
    this.statusBar.text = 'Stepping forward';
    try {
      const value = await this.langServer.stepForward(this.documentUri);
      this.view.update(value);
    } catch (err) {
    }
    this.statusBar.text = 'Ready';
  }

  public async stepBackward(editor: TextEditor) {
    this.statusBar.text = 'Stepping backward';
    try {
      const value = await this.langServer.stepBackward(this.documentUri);
      this.view.update(value);
      // const range = new vscode.Range(editor.document.positionAt(value.commandStart), editor.document.positionAt(value.commandEnd));
      // clearHighlight(editor, range);
    } catch (err) {
    }
    this.statusBar.text = 'Ready';
  }

  public async interpretToCursorPosition(editor: TextEditor) {
    this.statusBar.text = 'Interpretting to point';
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const value = await this.langServer.interpretToPoint(this.documentUri, editor.document.offsetAt(editor.selection.active));
      this.view.update(value);
    } catch (err) {
    }
    this.statusBar.text = 'Ready';
  }

  public async interpretToEnd(editor: TextEditor) {
    this.statusBar.text = 'Interpreting to end';
    try {
      const params = { uri: this.documentUri };
      const value = await this.langServer.interpretToEnd(this.documentUri);
      this.view.update(value);
    } catch (err) {
    }
    this.statusBar.text = 'Ready';
  }

  public async check(query: string) {
    const results = await this.langServer.check(this.documentUri, query);
    var a = results;
  }
  
  
  public async locate(query: string) {
    const results = await this.langServer.locate(this.documentUri, query);
    var a = results;
  }
  
  public async search(query: string) {
    const results = await this.langServer.search(this.documentUri, query);
    var a = results;
  }
  
  public async searchAbout(query: string) {
    const results = await this.langServer.searchAbout(this.documentUri, query);
    var a = results;
  }
}