'use strict';

import * as vscode from 'vscode';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient } from 'vscode-languageclient';
import * as vscodeTypes from 'vscode-languageserver-types';
import * as vc from 'vscode-languageclient';

import {Highlights} from './Highlights';
import {CoqView, SimpleCoqView} from './SimpleCoqView';
import {MDCoqView} from './MDCoqView';
import {HtmlCoqView} from './HtmlCoqView';
import {HtmlLtacProf} from './HtmlLtacProf';
import * as proto from './protocol';
import * as textUtil from './text-util';
import {CoqLanguageServer} from './CoqLanguageServer';
import {adjacentPane} from './CoqView';
import {StatusBar} from './StatusBar';


const STM_FOCUS_IMAGE = "./images/stm-focus.svg";
const STM_FOCUS_IMAGE_BEFORE = "./images/stm-focus-before.svg";

export class CoqDocument implements vscode.Disposable {
  private statusBar: StatusBar;
  public documentUri: string;
  public highlights = new Highlights();
  private viewDoc: vscode.TextDocument = null;
  private langServer: CoqLanguageServer;
  private view : CoqView;
  private infoOut: vscode.OutputChannel;
  private queryOut: vscode.OutputChannel;
  private noticeOut: vscode.OutputChannel;
  private cursorUnmovedSinceCommandInitiated = new Set<vscode.TextEditor>();
  private focusDecoration : vscode.TextEditorDecorationType;
  private focusBeforeDecoration : vscode.TextEditorDecorationType;

  constructor(uri: vscode.Uri, context: ExtensionContext) {
    this.statusBar = new StatusBar();
    this.viewDoc = vscode.workspace.textDocuments.find((doc) => doc.uri === uri);

    this.documentUri = uri.toString();
    this.langServer = new CoqLanguageServer(context);

    this.infoOut = vscode.window.createOutputChannel('Info');
    this.queryOut = vscode.window.createOutputChannel('Query Results');
    this.noticeOut = vscode.window.createOutputChannel('Notices');
    
    this.view = new HtmlCoqView(uri, context);
    // this.view = new SimpleCoqView(uri.toString());
    // this.view = new MDCoqView(uri);
    this.view.show(true,adjacentPane(this.currentViewColumn()));

    this.focusDecoration = vscode.window.createTextEditorDecorationType({
      gutterIconPath: context.asAbsolutePath(STM_FOCUS_IMAGE),
      gutterIconSize: "contain"
    });
    this.focusBeforeDecoration = vscode.window.createTextEditorDecorationType({
      gutterIconPath: context.asAbsolutePath(STM_FOCUS_IMAGE_BEFORE),
      gutterIconSize: "contain"
    });


    this.langServer.onUpdateHighlights((p) => this.onDidUpdateHighlights(p));
    this.langServer.onMessage((p) => this.onCoqMessage(p));
    this.langServer.onReset((p) => { if (p.uri == this.documentUri) this.onCoqReset(); });
    this.langServer.onUpdateCoqStmFocus((p) => { if (p.uri == this.documentUri) this.updateFocus(p.focus) });
    this.langServer.onUpdateComputingStatus((p) => { if (p.uri == this.documentUri) this.onUpdateComputingStatus(p); });
    this.langServer.onLtacProfResults((p) => { if (p.uri == this.documentUri) this.onLtacProfResults(p); });

    context.subscriptions.push(this.langServer.start());

    this.view.onresize = async (columns:number) => {
      await this.langServer.resizeView(this.documentUri,Math.floor(columns));
      const value = await this.langServer.getGoal(this.documentUri);
      this.view.update(value);
    };

    vscode.window.onDidChangeTextEditorSelection((e:vscode.TextEditorSelectionChangeEvent) => {
      if(this.cursorUnmovedSinceCommandInitiated.has(e.textEditor))
        this.cursorUnmovedSinceCommandInitiated.delete(e.textEditor);
    })
    
    if(vscode.window.activeTextEditor.document.uri.toString() == this.documentUri)
      this.statusBar.focus();
    this.statusBar.setStateReady();
  }
  
  public getUri() {
    return this.documentUri;
  }

  dispose() {
    this.statusBar.dispose();
    this.view.dispose();
    this.focusDecoration.dispose();
    this.focusBeforeDecoration.dispose();
  }

  private reset() {
    this.highlights.clearAllHighlights(this.allEditors())
  }

  private rememberCursors() {
    this.cursorUnmovedSinceCommandInitiated.clear();
    for(let editor of this.allEditors()) {
      this.cursorUnmovedSinceCommandInitiated.add(editor);    
    }
  }

  private onDidUpdateHighlights(params: proto.NotifyHighlightParams) {
    this.allEditors()
      .forEach((editor) => this.updateHighlights(editor,params));
  }
  
  
  private onUpdateComputingStatus(params: proto.NotifyComputingStatusParams) {
    this.statusBar.setStateComputing(params.status);
  }
  
  private onCoqMessage(params: proto.NotifyMessageParams) {
    switch(params.level) {
    case 'warning':
      // vscode.window.showWarningMessage(params.message); return;
      this.infoOut.show(true);
      this.infoOut.appendLine(params.message);
    case 'info':
      // this.infoOut.appendLine(params.message); return;
      // this.view.message(params.message);
      this.infoOut.show(true);
      this.infoOut.appendLine(params.message);
      return;
    case 'notice':
      this.noticeOut.clear();
      this.noticeOut.show(true);
      this.noticeOut.append(params.message);
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
    this.highlights.updateHighlights(this.allEditors(),params);
  }

  public async interruptCoq() {
    this.statusBar.setStateMessage('Killing CoqTop');
    try {
      await this.langServer.interruptCoq(this.documentUri);
    } finally {}
    this.statusBar.setStateReady();
  }

  public async quitCoq(editor: TextEditor) {
    this.statusBar.setStateMessage('Killing CoqTop');
    try {
      await this.langServer.quitCoq(this.documentUri);
    } finally {}
    this.reset();
    this.statusBar.setStateReady();
  }

  public async resetCoq(editor: TextEditor) {
    this.statusBar.setStateMessage('Resetting Coq');
    try {
      await this.langServer.resetCoq(this.documentUri);
    } finally {}
    this.reset();
    this.statusBar.setStateReady();
  }
  
  private findEditor() : vscode.TextEditor {
    return vscode.window.visibleTextEditors.find((editor,i,a) => 
      editor.document.uri.toString() === this.documentUri);
  }

  public allEditors() : vscode.TextEditor[] {
    return vscode.window.visibleTextEditors.filter((editor,i,a) => 
      editor.document.uri.toString() === this.documentUri)
  }

  private currentViewColumn() {
    let editor = this.findEditor();
    if(editor)
      return editor.viewColumn;
    else
      return vscode.window.activeTextEditor.viewColumn;
  }
  
  private onCoqReset() {
    this.reset();
    this.statusBar.setStateReady();
  }

  private updateFocus(focus?: vscodeTypes.Position, moveCursor = false) {
    if(focus) {
      const focusPos = new vscode.Position(focus.line,focus.character);
      if(moveCursor) {
        for(let editor of this.cursorUnmovedSinceCommandInitiated)
          editor.selections = [new vscode.Selection(focusPos, focusPos)]
      }
      if(focusPos.line === 0 && focus.character === 0) {
        for(let editor of this.allEditors()) {
          editor.setDecorations(this.focusBeforeDecoration, [new vscode.Range(focusPos,focusPos.translate(0,1))]);
          editor.setDecorations(this.focusDecoration, []);
        }
      } else {
        for(let editor of this.allEditors()) {
          editor.setDecorations(this.focusBeforeDecoration, []);
          editor.setDecorations(this.focusDecoration, [new vscode.Range(focusPos,focusPos.translate(0,1))]);
        }
      }
    } else {
      for(let editor of this.allEditors())
        editor.setDecorations(this.focusDecoration, []);
    }
  }

  public async stepForward(editor: TextEditor) {
    this.statusBar.setStateWorking('Stepping forward');
    try {
      this.rememberCursors();
      const value = await this.langServer.stepForward(this.documentUri);
      this.view.update(value);
      if(value.type !== 'not-running')
        this.updateFocus(value.focus, true);
      if(value.type === 'interrupted')
        this.statusBar.setStateComputing(proto.ComputingStatus.Interrupted)
    } catch (err) {
    }
    this.statusBar.setStateReady();
  }

  public async stepBackward(editor: TextEditor) {
    this.statusBar.setStateWorking('Stepping backward');
    try {
      this.rememberCursors();
      const value = await this.langServer.stepBackward(this.documentUri);
      this.view.update(value);
      if(value.type !== 'not-running')
        this.updateFocus(value.focus, true)
      if(value.type === 'interrupted')
        this.statusBar.setStateComputing(proto.ComputingStatus.Interrupted)
      // const range = new vscode.Range(editor.document.positionAt(value.commandStart), editor.document.positionAt(value.commandEnd));
      // clearHighlight(editor, range);
    } catch (err) {
    }
    this.statusBar.setStateReady();
  }

  public async interpretToCursorPosition(editor: TextEditor) {
    this.statusBar.setStateWorking('Interpretting to point');
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const value = await this.langServer.interpretToPoint(this.documentUri, editor.document.offsetAt(editor.selection.active));
      if(value.type !== 'not-running')
        this.updateFocus(value.focus);
      if(value.type === 'interrupted')
        this.statusBar.setStateComputing(proto.ComputingStatus.Interrupted)
      this.view.update(value);
    } catch (err) {
    }
    this.statusBar.setStateReady();
  }

  public async interpretToEnd(editor: TextEditor) {
    this.statusBar.setStateWorking('Interpreting to end');
    try {
      const params = { uri: this.documentUri };
      const value = await this.langServer.interpretToEnd(this.documentUri);
      if(value.type !== 'not-running')
        this.updateFocus(value.focus,true);
      if(value.type === 'interrupted')
        this.statusBar.setStateComputing(proto.ComputingStatus.Interrupted)
      this.view.update(value);
    } catch (err) { }
    this.statusBar.setStateReady();
  }

  public async check(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      return await this.langServer.check(this.documentUri, query);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  private displayQueryResults(results: proto.CoqTopQueryResult) {
    this.queryOut.clear();
    this.queryOut.show(true);
    this.queryOut.append(results.searchResults);
    
  }
  
  public async locate(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.locate(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async search(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.search(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async searchAbout(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.searchAbout(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async viewGoalState(editor: TextEditor, external: boolean) {
    try {
      if(external) {
        await this.view.showExternal();
      } else
        await this.view.show(true,adjacentPane(editor.viewColumn));
    } catch (err) {}
  }

  public async ltacProfGetResults(editor: TextEditor) {
    this.statusBar.setStateWorking('Running query');
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const offset = editor.document.offsetAt(editor.selection.active);
      const results = await this.langServer.ltacProfGetResults(this.documentUri,offset);
      // const view = new HtmlLtacProf(results); 
      // const out = vscode.window.createOutputChannel("LtacProfiler");
      // results.forEach((value,key) => {
      //     out.appendLine("-----------------------------------");
      //     this.outputLtacProfTreeNode(out, "", key, value);
      //   });
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  private onLtacProfResults(params: proto.NotifyLtacProfResultsParams) {
    const view = new HtmlLtacProf(params.results); 
  }

  public async doOnLostFocus() {
    this.statusBar.unfocus();
  }  

  public async doOnFocus(editor: TextEditor) {
    this.highlights.refreshHighlights([editor]);
    this.statusBar.focus();
    // await this.view.show(true);
  }

  public async doOnSwitchActiveEditor(oldEditor: TextEditor, newEditor: TextEditor) {
    this.highlights.refreshHighlights([newEditor]);
  }
}