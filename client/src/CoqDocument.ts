'use strict';

import * as vscode from 'vscode';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient } from 'vscode-languageclient';


import {Highlights} from './Highlights';
import {CoqView, SimpleCoqView} from './SimpleCoqView';
import {MDCoqView} from './MDCoqView';
import {HtmlCoqView} from './HtmlCoqView';
import {HtmlLtacProf} from './HtmlLtacProf';
import * as proto from './protocol';
import * as textUtil from './text-util';
import {CoqLanguageServer} from './CoqLanguageServer';




export class CoqDocument implements vscode.Disposable {
  private statusBar: vscode.StatusBarItem;
  private computingStatusBar: vscode.StatusBarItem;
  private interruptButtonStatusBar: vscode.StatusBarItem;
  public documentUri: string;
  public highlights = new Highlights();
  private viewDoc: vscode.TextDocument = null;
  private langServer: CoqLanguageServer;
  private view : CoqView;
  private infoOut: vscode.OutputChannel;
  private queryOut: vscode.OutputChannel;
  private noticeOut: vscode.OutputChannel;

  constructor(uri: vscode.Uri, context: ExtensionContext) {
    this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 3);
    this.statusBar.text = 'Loading Coq';
    this.statusBar.show();
    this.computingStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 2);
    this.computingStatusBar.tooltip = 'Time elapsed on the current computation';
    this.computingStatusBar.text = '';
    this.interruptButtonStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 1);
    this.interruptButtonStatusBar.tooltip = 'Interrupt Coq computation';
    this.interruptButtonStatusBar.color = 'rgba(255,100,100,1)';
    this.interruptButtonStatusBar.command = 'extension.coq.interrupt';
    this.interruptButtonStatusBar.text = '$(primitive-square)';

    this.documentUri = uri.toString();
    this.langServer = new CoqLanguageServer(context);

    this.infoOut = vscode.window.createOutputChannel('Info');
    this.queryOut = vscode.window.createOutputChannel('Query Results');
    this.noticeOut = vscode.window.createOutputChannel('Notices');
    
    this.view = new HtmlCoqView(uri, context);
    // this.view = new SimpleCoqView(uri.toString());
    // this.view = new MDCoqView(uri);


    this.langServer.onUpdateHighlights((p) => this.onDidUpdateHighlights(p));
    this.langServer.onMessage((p) => this.onCoqMessage(p));
    this.langServer.onReset((p) => { if (p.uri == this.documentUri) this.onCoqReset(); });
    this.langServer.onUpdateStateViewUrl((p) => { if (p.uri == this.documentUri) this.updateStateViewUrl(p.stateUrl); });
    this.langServer.onUpdateComputingStatus((p) => { if (p.uri == this.documentUri) this.onUpdateComputingStatus(p); });

    context.subscriptions.push(this.langServer.start());

    this.view.onresize = async (columns:number) => {
      await this.langServer.resizeView(this.documentUri,Math.floor(columns));
      const value = await this.langServer.getGoal(this.documentUri);
      this.view.update(value);
    };
    
    this.statusBar.text = 'Ready';
    
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
    this.interruptButtonStatusBar.dispose();
    this.computingStatusBar.dispose();
    this.statusBar.dispose();
    this.view.dispose();
  }

  private reset() {
    this.highlights.clearAllHighlights(this.allEditors())
  }

  private onDidUpdateHighlights(params: proto.NotifyHighlightParams) {
    this.updateHighlights(this.findEditor(),params);
  }
  
  
  private onUpdateComputingStatus(params: proto.NotifyComputingStatusParams) {
    switch(params.status) {
      case proto.ComputingStatus.Finished:
        this.computingStatusBar.hide();
        this.interruptButtonStatusBar.hide();
        break;
      case proto.ComputingStatus.Computing:
        if(params.computeTimeMS > 2000) {
          this.computingStatusBar.text = `[${textUtil.formatTimeSpanMS(params.computeTimeMS)}]`;
          this.computingStatusBar.show();
          this.interruptButtonStatusBar.show();
        }
        break;
      case proto.ComputingStatus.Interrupted:
        this.computingStatusBar.text = `[Interrupted $(watch) ${textUtil.formatTimeSpanMS(params.computeTimeMS)}]`;
        this.computingStatusBar.show();
        this.interruptButtonStatusBar.hide();
        break;
    }
    
  }
  
  private onCoqMessage(params: proto.NotifyMessageParams) {
    switch(params.level) {
    case 'warning':
      vscode.window.showWarningMessage(params.message); return;
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
    this.setStatusBarWorking('Killing CoqTop');
    try {
      await this.langServer.interruptCoq(this.documentUri);
    } finally {}
    this.setStatusBarReady();
  }

  private setStatusBarReady() {
    this.statusBar.text = 'Ready';
    this.interruptButtonStatusBar.hide();
  }

  private setStatusBarWorking(name: string) {
    this.computingStatusBar.hide();
    this.interruptButtonStatusBar.hide();
    this.statusBar.text = name;
  }

  public async quitCoq(editor: TextEditor) {
    this.setStatusBarWorking('Killing CoqTop');
    try {
      await this.langServer.quitCoq(this.documentUri);
    } finally {}
    this.reset();
    this.setStatusBarReady();
  }

  public async resetCoq(editor: TextEditor) {
    this.setStatusBarWorking('Resetting Coq');
    try {
      await this.langServer.resetCoq(this.documentUri);
    } finally {}
    this.reset();
    this.setStatusBarReady();
  }
  
  private findEditor() : vscode.TextEditor {
    return vscode.window.visibleTextEditors.find((editor,i,a) => 
      editor.document.uri.toString() === this.documentUri)
  }

  public allEditors() : vscode.TextEditor[] {
    return vscode.window.visibleTextEditors.filter((editor,i,a) => 
      editor.document.uri.toString() === this.documentUri)
  }
  
  private onCoqReset() {
    this.reset();
    this.setStatusBarReady();
  }

  public async stepForward(editor: TextEditor) {
    this.setStatusBarWorking('Stepping forward');
    try {
      const value = await this.langServer.stepForward(this.documentUri);
      this.view.update(value);
    } catch (err) {
    }
    this.setStatusBarReady();
  }

  public async stepBackward(editor: TextEditor) {
    this.setStatusBarWorking('Stepping backward');
    try {
      const value = await this.langServer.stepBackward(this.documentUri);
      this.view.update(value);
      // const range = new vscode.Range(editor.document.positionAt(value.commandStart), editor.document.positionAt(value.commandEnd));
      // clearHighlight(editor, range);
    } catch (err) {
    }
    this.setStatusBarReady();
  }

  public async interpretToCursorPosition(editor: TextEditor) {
    this.setStatusBarWorking('Interpretting to point');
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const value = await this.langServer.interpretToPoint(this.documentUri, editor.document.offsetAt(editor.selection.active));
      this.view.update(value);
    } catch (err) {
    }
    this.setStatusBarReady();
  }

  public async interpretToEnd(editor: TextEditor) {
    this.setStatusBarWorking('Interpreting to end');
    try {
      const params = { uri: this.documentUri };
      const value = await this.langServer.interpretToEnd(this.documentUri);
      this.view.update(value);
    } catch (err) { }
    this.setStatusBarReady();
  }

  public async check(query: string) {
    this.setStatusBarWorking('Running query');
    try {
      return await this.langServer.check(this.documentUri, query);
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  private displayQueryResults(results: proto.CoqTopQueryResult) {
    this.queryOut.clear();
    this.queryOut.show(true);
    this.queryOut.append(results.searchResults);
    
  }
  
  public async locate(query: string) {
    this.setStatusBarWorking('Running query');
    try {
      const results = await this.langServer.locate(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  public async search(query: string) {
    this.setStatusBarWorking('Running query');
    try {
      const results = await this.langServer.search(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  public async searchAbout(query: string) {
    this.setStatusBarWorking('Running query');
    try {
      const results = await this.langServer.searchAbout(this.documentUri, query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  public async viewGoalState(editor: TextEditor, external: boolean) {
    try {
      if(external) {
        await this.view.showExternal();
      } else
        await this.view.show(true);
    } catch (err) {}
  }

  public async ltacProfSet(enabled: boolean) {
    this.setStatusBarWorking('Running query');
    try {
      await this.langServer.ltacProfSet(this.documentUri, enabled);
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  public async ltacProfGetResults(editor: TextEditor) {
    this.setStatusBarWorking('Running query');
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const offset = editor.document.offsetAt(editor.selection.active);
      const results = await this.langServer.ltacProfGetResults(this.documentUri,offset);
      const view = new HtmlLtacProf(results); 
      // const out = vscode.window.createOutputChannel("LtacProfiler");
      // results.forEach((value,key) => {
      //     out.appendLine("-----------------------------------");
      //     this.outputLtacProfTreeNode(out, "", key, value);
      //   });
    } catch (err) {
    } finally {
      this.setStatusBarReady();
    }
  }
  
  public async doOnLostFocus() {
  }  

  public async doOnFocus(editor: TextEditor) {
    // await this.view.show(true);
  }  
}