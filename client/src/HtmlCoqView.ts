'use strict';
import * as vscode from 'vscode'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import {extensionContext} from './extension'
import * as proto from './protocol'
import * as WebSocket from 'ws';
import * as path from 'path';
import * as docs from './CoqProject';
import * as nasync from './nodejs-async';
import * as webServer from './WebServer';
import * as psm from './prettify-symbols-mode';

const opener = require('opener');
import mustache = require('mustache');

interface ControllerEvent {
  eventName: string;
  params: ResizeEvent // | | | | | ;
}

interface ResizeEvent {
  columns: number;
}

interface GoalUpdate {
  command: 'goal-update',
  goal: proto.CommandResult
}

interface SettingsUpdate extends SettingsState {
  command: 'settings-update'
}

interface SettingsState {
  fontFamily?: string,
  fontSize?: string,
  fontWeight?: string,
  cssFile?: string,
  prettifySymbolsMode?: boolean,
}


type ProofViewProtocol = GoalUpdate | SettingsUpdate;

const VIEW_PATH = 'html_views';

function proofViewCSSFile() {
  const userDir = vscode.workspace.getConfiguration("coq.hacks")
    .get("userSettingsLocation", null)
    || extensionContext.asAbsolutePath(path.join(VIEW_PATH,'goals'));
  return vscode.Uri.file(path.join(userDir,'proof-view.css'));
}

function proofViewFile(file: string = "") {
  return vscode.Uri.file(extensionContext.asAbsolutePath(path.join(VIEW_PATH,'goals',file)));
}

function proofViewHtmlPath() {
  return proofViewFile('Coq.html');
}


function coqViewToFileUri(uri: vscode.Uri) {
  return `vscode-resource://${uri.path}?${uri.query}#${uri.fragment}`;
}

/**
 * Displays a Markdown-HTML file which contains javascript to connect to this view
 * and update the goals and show other status info
 */
export class HtmlCoqView implements view.CoqView {
  private docUri: vscode.Uri;
  private coqViewUri : vscode.Uri;
  private currentSettings : SettingsState = {};
  private visible = false;

  private panel : vscode.WebviewPanel | null = null;

  private resizeEvent = new vscode.EventEmitter<number>();

  public get resize() : vscode.Event<number> { return this.resizeEvent.event; }

  constructor(uri: vscode.Uri, context: vscode.ExtensionContext) {
    context.subscriptions.push(vscode.workspace.onDidChangeConfiguration(() => this.updateSettings()))

    this.docUri = uri;

    psm.onEnabledChange((enabled) => {
      this.currentSettings.prettifySymbolsMode = enabled;
      this.sendMessage(Object.assign<SettingsState,{command: 'settings-update'}>({prettifySymbolsMode: enabled},{command: 'settings-update'}));
    });
  }

  private handleClientResize(event: ResizeEvent) {
    this.resizeEvent.fire(event.columns);
  }

  private handleClientMessage(event: {data: any; type: string; target: WebSocket}) {
    const message = <ControllerEvent>JSON.parse(event.data);
    switch(message.eventName) {
      case 'resize':
        this.handleClientResize(message.params);
        return;
      case 'focus':
        docs.getProject().setActiveDoc(this.docUri);
        return;
    }
  }


  private async createBuffer() : Promise<void> {
    try {
      await HtmlCoqView.prepareStyleSheet();
      this.coqViewUri = vscode.Uri.parse(`file://${proofViewHtmlPath().path.replace(/%3A/, ':')}`);
      console.log("Goals: " + decodeURIComponent(this.coqViewUri.with({scheme: 'file'}).toString()));
    } catch(err) {
      vscode.window.showErrorMessage(err.toString());
    }
  }

  public getUri() : vscode.Uri {
    return this.coqViewUri;
  }

  public isVisible() {
    return this.visible;
  }

  public async initializePanel(pane: vscode.ViewColumn) {
    if (this.panel === null) {
      this.panel = vscode.window.createWebviewPanel(
        'html_coq',
        "ProofView: " + path.basename(this.docUri.fsPath),
        pane,
        {enableScripts: true}
      );

      let doc = await vscode.workspace.openTextDocument(this.coqViewUri);

      this.panel.webview.html = mustache.render(doc.getText(), {extensionPath: extensionContext.asAbsolutePath(VIEW_PATH)});

      this.panel.webview.onDidReceiveMessage(message => this.handleClientMessage(message));
    }
  }

  public async show(preserveFocus: boolean, pane: vscode.ViewColumn) {
    if(!this.coqViewUri)
      await this.createBuffer();

    this.initializePanel(pane);

    this.visible = true;
  }

  public async showExternal(scheme: "file"|"http", command? : (url:string)=>{module: string, args: string[]}) : Promise<void> {
    let url : string;
    if(scheme === "file") {
      url = decodeURIComponent(coqViewToFileUri(this.coqViewUri).toString());
    } else {
            // this.coqViewUri = vscode.Uri.parse(`coq-view://${proofViewHtmlPath().path.replace(/%3A/, ':')}?host=${serverAddress.address}&port=${serverAddress.port}`);
      const uri = await webServer.serveDirectory("proof-view/", proofViewFile('..').fsPath, "**/*.{html,css,js}");
      if(!uri)
        return Promise.reject("Cannot find proof view script");
      url = decodeURIComponent(uri.with({path: uri.path + 'goals/Coq.html', query: this.coqViewUri.query, fragment: this.coqViewUri.fragment }).toString());
    }
    if(!command)
      return Promise.resolve(opener(url));
    else {
      const c = command(url);
      return Promise.resolve(opener(c.args.join(' '), {command: c.module}));
    }
  }

  public dispose() {
    if (this.panel !== null)
      this.panel.dispose()
  }

  private async sendMessage(message: ProofViewProtocol) {
    if (this.panel !== null)
      this.panel.webview.postMessage(message);
  }

  private async updateClient(state: proto.CommandResult) {
    await this.sendMessage({command: 'goal-update', goal: state});
  }

  public update(state: proto.CommandResult) {
    this.updateClient(state);
  }


  private async updateSettings() {
    this.currentSettings.fontFamily = vscode.workspace.getConfiguration("editor").get("fontFamily") as string;
    this.currentSettings.fontSize = `${vscode.workspace.getConfiguration("editor").get("fontSize") as number}pt`;
    this.currentSettings.fontWeight = vscode.workspace.getConfiguration("editor").get("fontWeight") as string;
    this.currentSettings.cssFile = decodeURIComponent(proofViewCSSFile().toString());
    this.currentSettings.prettifySymbolsMode = psm.isEnabled();
    await this.sendMessage(Object.assign<SettingsState,{command: 'settings-update'}>(this.currentSettings,{command: 'settings-update'}));
  }

  private static async shouldResetStyleSheet() : Promise<boolean> {
    try {
      const styleFile = proofViewCSSFile();
      if(!await nasync.fs.exists(styleFile.fsPath))
        return true;
      const stat = await nasync.fs.stat(styleFile.fsPath);
      if(stat.size < 5 && (await nasync.fs.readFile(styleFile.fsPath, 'utf8')).trim() === "")
        return true;
    } catch(err) {
      console.error(err.toString());
    }
    return false;
  }

  /** makes sure that the style sheet is available */
  private static async prepareStyleSheet() {
    try {
      const styleFile = proofViewCSSFile();
      if(await HtmlCoqView.shouldResetStyleSheet() === true) {
        const defaultFile = proofViewFile('default-proof-view.css');
        await nasync.fs.copyFile(defaultFile.fsPath,styleFile.fsPath);
      }
    } catch(err) {
      console.error(err.toString());
    }
  }


  public static async customizeProofViewStyle() {
    try {
      await HtmlCoqView.prepareStyleSheet();
      const styleFile = proofViewCSSFile();
      const doc = await vscode.workspace.openTextDocument(styleFile.fsPath);
      await vscode.window.showTextDocument(doc);
    } catch(err) {
      console.error(err.toString());
    }
  }
}
