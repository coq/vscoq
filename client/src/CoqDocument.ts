'use strict';

import * as vscode from 'vscode';
import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient } from 'vscode-languageclient';
import * as vscodeTypes from 'vscode-languageserver-types';
import * as vc from 'vscode-languageclient';

import {decorations} from './Decorations';
import {Highlights} from './Highlights';
import {CoqView, SimpleCoqView} from './SimpleCoqView';
import {MDCoqView} from './MDCoqView';
import {HtmlCoqView} from './HtmlCoqView';
import {HtmlLtacProf} from './HtmlLtacProf';
import * as proto from './protocol';
import * as textUtil from './text-util';
import {extensionContext} from './extension';
import {CoqDocumentLanguageServer} from './CoqLanguageServer';
import {adjacentPane} from './CoqView';
import {StatusBar} from './StatusBar';
import {CoqProject} from './CoqProject';
import * as text from './AnnotatedText';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

namespace DisplayOptionPicks {
  type T = vscode.QuickPickItem & {displayItem: number};
  export const ImplicitArguments : T =
  { label: "Implicit Arguments", description: "toggle display of *implicit arguments*", detail: "some detail", displayItem: proto.DisplayOption.ImplicitArguments };
  export const Coercions : T =
  { label: "Coercions", description: "toggle display of *coercions*", displayItem: proto.DisplayOption.Coercions };
  export const RawMatchingExpressions : T =
  { label: "Raw Matching Expressions", description: "toggle display of *raw matching expressions*", displayItem: proto.DisplayOption.RawMatchingExpressions };
  export const Notations : T =
  { label: "Notations", description: "toggle display of notations", displayItem: proto.DisplayOption.Notations };
  export const AllBasicLowLevelContents : T =
  { label: "All Basic Low Level Contents", description: "toggle display of ", displayItem: proto.DisplayOption.AllBasicLowLevelContents };
  export const ExistentialVariableInstances : T =
  { label: "Existential Variable Instances", description: "toggle display of ", displayItem: proto.DisplayOption.ExistentialVariableInstances };
  export const UniverseLevels : T =
  { label: "Universe Levels", description: "toggle display of ", displayItem: proto.DisplayOption.UniverseLevels };
  export const AllLowLevelContents : T =
  { label: "All Low Level Contents", description: "toggle display of ", displayItem: proto.DisplayOption.AllLowLevelContents };
  export const allPicks = [ImplicitArguments, Coercions, RawMatchingExpressions, Notations, AllBasicLowLevelContents, ExistentialVariableInstances, UniverseLevels, AllLowLevelContents];
}

export class CoqDocument implements vscode.Disposable {
  /** A list of things to dispose */
  private subscriptions : Disposable[] = []
  private statusBar: StatusBar;
  public documentUri: string;
  public highlights = new Highlights();
  private document: vscode.TextDocument = null;
  private langServer: CoqDocumentLanguageServer;
  private view : CoqView;
  private infoOut: vscode.OutputChannel;
  private queryOut: vscode.OutputChannel;
  private noticeOut: vscode.OutputChannel;
  private cursorUnmovedSinceCommandInitiated = new Set<vscode.TextEditor>();
  private focus: vscode.Position;
  private project: CoqProject;
  private currentLtacProfView: HtmlLtacProf = null;

  constructor(document: vscode.TextDocument, project: CoqProject) {
    this.statusBar = new StatusBar();
    this.document = document;
    this.project = project;
    // this.document = vscode.workspace.textDocuments.find((doc) => doc.uri === uri);

    this.documentUri = document.uri.toString();
    this.langServer = new CoqDocumentLanguageServer(document.uri.toString());

    this.infoOut = vscode.window.createOutputChannel('Info');
    this.queryOut = vscode.window.createOutputChannel('Query Results');
    this.noticeOut = vscode.window.createOutputChannel('Notices');
    
    this.view = new HtmlCoqView(document.uri, extensionContext);
    // this.view = new SimpleCoqView(uri.toString());
    // this.view = new MDCoqView(uri);
    this.view.show(true,adjacentPane(this.currentViewColumn()));

    this.langServer.onUpdateHighlights((p) => this.onDidUpdateHighlights(p));
    this.langServer.onMessage((p) => this.onCoqMessage(p));
    this.langServer.onReset((p) => this.onCoqReset());
    this.langServer.onUpdateCoqStmFocus((p) => this.updateFocus(p.position));
    this.langServer.onLtacProfResults((p) => this.onLtacProfResults(p));

    this.view.onresize = async (columns:number) => {
      try {
        await this.langServer.resizeView(Math.floor(columns));
        const value = await this.langServer.getGoal();
        this.view.update(value);
      } catch(err) {}
    };

    this.subscriptions.push(vscode.window.onDidChangeTextEditorSelection((e:vscode.TextEditorSelectionChangeEvent) => {
      if(this.cursorUnmovedSinceCommandInitiated.has(e.textEditor))
        this.cursorUnmovedSinceCommandInitiated.delete(e.textEditor);
    }));

    if(vscode.window.activeTextEditor.document.uri.toString() == this.documentUri)
      this.statusBar.focus();
    this.statusBar.setStateReady();
  }
  
  public getUri() {
    return this.documentUri;
  }

  public getDocument() {
    return this.document;
  }

  public dispose() {
    this.highlights.clearAll(this.allEditors());
    this.statusBar.dispose();
    this.view.dispose();
    this.subscriptions.forEach((d) => d.dispose());
  }

  private reset() {
    this.highlights.clearAll(this.allEditors())
  }

  private rememberCursors() {
    this.cursorUnmovedSinceCommandInitiated.clear();
    for(let editor of this.allEditors()) {
      this.cursorUnmovedSinceCommandInitiated.add(editor);    
    }
  }

  private onDidUpdateHighlights(params: proto.Highlights) {
    this.highlights.set(this.allEditors(),params);
  }
  
  
  // private onUpdateComputingStatus(params: proto.NotifyComputingStatusParams) {
  //   this.statusBar.setStateComputing(params.status);
  // }
  
  private onCoqMessage(params: proto.NotifyMessageParams) {
    switch(params.level) {
    case 'warning':
      // vscode.window.showWarningMessage(params.message); return;
      this.infoOut.show(true);
      this.infoOut.appendLine(text.textToDisplayString(params.message));
    case 'info':
      // this.infoOut.appendLine(params.message); return;
      // this.view.message(params.message);
      this.infoOut.show(true);
      this.infoOut.appendLine(text.textToDisplayString(params.message));
      return;
    case 'notice':
      this.noticeOut.clear();
      this.noticeOut.show(true);
      this.noticeOut.append(text.textToDisplayString(params.message));
      return;
      // vscode.window.showInformationMessage(params.message); return;
    // case 'error':
    //   vscode.window.showErrorMessage(text.textToDisplayString(params.message)); return;
    }
  }


  public onDidChangeTextDocument(params: vscode.TextDocumentChangeEvent) {
    this.updateFocus(this.focus, false);
  }


  public async interruptCoq() {
    this.statusBar.setStateMessage('Killing CoqTop');
    try {
      await this.langServer.interruptCoq();
    } finally {}
    this.statusBar.setStateReady();
  }

  public async quitCoq(editor: TextEditor) {
    this.statusBar.setStateMessage('Killing CoqTop');
    try {
      await this.langServer.quitCoq();
    } finally {}
    this.reset();
    this.statusBar.setStateReady();
  }

  public async resetCoq(editor: TextEditor) {
    this.statusBar.setStateMessage('Resetting Coq');
    try {
      await this.langServer.resetCoq();
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

  /** Bring the focus into the editor's view, but only scroll rightward
   * if the focus is not at the end of a line
   * */
  public setCursorToFocus(editor: vscode.TextEditor, scroll: boolean = true, scrollHorizontal = false) {
    if(!editor)
      return;
    editor.selections = [new vscode.Selection(this.focus, this.focus)]
    if(scroll) {
      if (scrollHorizontal || textUtil.positionIsBefore(this.focus, this.document.lineAt(this.focus.line).range.end))
        editor.revealRange(new vscode.Range(this.focus, this.focus), vscode.TextEditorRevealType.Default)
      else
        editor.revealRange(new vscode.Range(this.focus.line, 0, this.focus.line + 1, 0), vscode.TextEditorRevealType.Default)
    }
  }

  private updateFocus(focus?: vscodeTypes.Position, moveCursor = false) {
    if(focus) {
      this.focus = new vscode.Position(focus.line,focus.character);
      if(moveCursor) {
        // adjust the cursor position
        for(let editor of this.cursorUnmovedSinceCommandInitiated)
          this.setCursorToFocus(editor, editor === vscode.window.activeTextEditor);
      }

      // update the focus decoration
      const focusRange = new vscode.Range(this.focus.line,0,this.focus.line,1);
      if(this.focus.line === 0 && focus.character === 0) {
        for(let editor of this.allEditors()) {
          editor.setDecorations(decorations.focusBefore, [focusRange]);
          editor.setDecorations(decorations.focus, []);
        }
      } else {
        for(let editor of this.allEditors()) {
          editor.setDecorations(decorations.focusBefore, []);
          editor.setDecorations(decorations.focus, [focusRange]);
        }
      }
    } else {
      for(let editor of this.allEditors())
        editor.setDecorations(decorations.focus, []);
    }
  }

  private async userSetCoqtopPath(global = false) {
    const current = vscode.workspace.getConfiguration("coqtop").get("binPath", "");
    const newPath = await vscode.window.showInputBox({ignoreFocusOut: true, value: current, validateInput: v => {
      try {
        const statDir = fs.statSync(v);
        if(!statDir.isDirectory())
          return "not a directory";
      } catch(err) {
        return "invalid path";
      }
      let stat : fs.Stats = undefined;
      try {
        stat = fs.statSync(path.join(v, 'coqtop'));
      } catch(err) {}
      if(!stat && os.platform()==='win32') {
        try {
          stat = fs.statSync(path.join(v, 'coqtop.exe'));
        } catch(err) { }        
      }
      if(!stat)
        return "coqtop not found here"
      if(!stat.isFile())
        return "coqtop found here, but is not an executable file";

      return null;
    } });
    async function checkCoqtopExists(newPath: string) {
      if(!newPath)
        return false;
      try {
        return await fs.existsSync(path.join(newPath, 'coqtop')) || await fs.existsSync(path.join(newPath, 'coqtop.exe'))
      } catch(err) {
        return false;
      } 
    } 

    if(await checkCoqtopExists(newPath))
      await vscode.workspace.getConfiguration("coqtop").update("binPath", newPath, global);
  }

  private handleResult(value: proto.CommandResult) {
    if(value.type === 'busy')
      return false;
    if(value.type === 'not-running') {
      this.updateFocus(undefined, false);
      if(value.reason === 'spawn-failed') {
        const getCoq = {title: "Get Coq", id: 0};
        const setPathLocal = {title: "Set path for this project", id: 1};
        const setPathGlobal = {title: "Set path globally", id: 2};
        vscode.window.showErrorMessage(`Could not start coqtop ${value.coqtop ? ` (${value.coqtop})` : ""}`, getCoq, setPathLocal, setPathGlobal)
          .then(async act => {
            if(act && act.id === getCoq.id) {
              vscode.commands.executeCommand("vscode.open", vscode.Uri.parse('https://coq.inria.fr/download'))
            } else if(act && (act.id === setPathLocal.id || act.id === setPathGlobal.id)) {
              await this.userSetCoqtopPath(act.id === setPathGlobal.id);
            }
          })
      }
    } else
      this.updateFocus(value.focus, this.project.settings.moveCursorToFocus);
    if(value.type === 'interrupted')
      this.statusBar.setStateComputing(proto.ComputingStatus.Interrupted)

    return true;
  }

  public async stepForward(editor: TextEditor) {
    this.statusBar.setStateWorking('Stepping forward');
    try {
      this.rememberCursors();
      const value = await this.langServer.stepForward();
      this.view.update(value);
      this.handleResult(value);
    } catch (err) {
    }
    this.statusBar.setStateReady();
  }

  public async stepBackward(editor: TextEditor) {
    this.statusBar.setStateWorking('Stepping backward');
    try {
      this.rememberCursors();
      const value = await this.langServer.stepBackward();
      this.view.update(value);
      if(this.handleResult(value))
        this.statusBar.setStateReady();
      // const range = new vscode.Range(editor.document.positionAt(value.commandStart), editor.document.positionAt(value.commandEnd));
      // clearHighlight(editor, range);
    } catch (err) {
    }
  }

  public async finishComputations(editor: TextEditor) {
    this.statusBar.setStateWorking('Finishing computations');
    try {
      const value = await this.langServer.finishComputations();
      this.statusBar.setStateReady();
    } catch (err) {
    }
  }

  public async interpretToCursorPosition(editor: TextEditor, synchronous = false) {
    this.statusBar.setStateWorking('Interpretting to point');
    try {
      if(!editor || editor.document.uri.toString() !== this.documentUri)
       return;
      const value = await this.langServer.interpretToPoint(editor.selection.active, synchronous);
      this.view.update(value);
      this.handleResult(value);
    } catch (err) {
      console.warn("Interpret to point failed: " + err.toString());
      if(err.stack)
        console.log("Stack: \n" + err.stack);
    }
    this.statusBar.setStateReady();
  }

  public async interpretToEnd(editor: TextEditor, synchronous = false) {
    this.statusBar.setStateWorking('Interpreting to end');
    try {
      const params = { uri: this.documentUri };
      const value = await this.langServer.interpretToEnd(synchronous);
      this.view.update(value);
      this.handleResult(value);
    } catch (err) { }
    this.statusBar.setStateReady();
  }

  public async check(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.check(query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async print(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.print(query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  private displayQueryResults(results: proto.CoqTopQueryResult) {
    this.queryOut.clear();
    this.queryOut.show(true);
    this.queryOut.append(text.textToDisplayString(results.searchResults));
    
  }
  
  public async locate(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.locate(query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async search(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.search(query);
      this.displayQueryResults(results);
    } catch (err) {
    } finally {
      this.statusBar.setStateReady();
    }
  }
  
  public async searchAbout(query: string) {
    this.statusBar.setStateWorking('Running query');
    try {
      const results = await this.langServer.searchAbout(query);
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
      this.currentLtacProfView = new HtmlLtacProf({total_time: 0, tactics: []});
      this.currentLtacProfView.show(true);
      await this.langServer.ltacProfGetResults(offset);
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

  private onLtacProfResults(results: proto.LtacProfResults) {
    if(!this.currentLtacProfView)
      this.currentLtacProfView = new HtmlLtacProf(results);
    else 
      this.currentLtacProfView.update(results);
  }

  public async doOnLostFocus() {
    this.statusBar.unfocus();
  }  

  public async doOnFocus(editor: TextEditor) {
    this.highlights.refresh([editor]);
    this.statusBar.focus();
    // await this.view.show(true);
  }

  public async doOnSwitchActiveEditor(oldEditor: TextEditor, newEditor: TextEditor) {
    this.highlights.refresh([newEditor]);
  }

  private async queryDisplayOptionChange() : Promise<proto.DisplayOption|null> {
      const result = await vscode.window.showQuickPick(DisplayOptionPicks.allPicks);
      return result.displayItem;
  }

  public async setDisplayOption(item?: proto.DisplayOption, value?: proto.SetDisplayOption) {
    if(!item && !value) {
      item = await this.queryDisplayOptionChange();
      if(!item)
        return;
      value = proto.SetDisplayOption.Toggle
    }
    try {
      await this.langServer.setDisplayOptions([{item: item, value: value}]);
      const proofview = await this.langServer.getGoal();
      this.view.update(proofview);
    } catch(err) { }
 }
  
}