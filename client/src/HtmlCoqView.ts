'use strict';
import * as vscode from 'vscode'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import {extensionContext} from './extension'
import * as proto from './protocol'
import * as WebSocket from 'ws';
import * as http from 'http';
import * as path from 'path';
import * as docs from './CoqProject';
import * as nasync from './nodejs-async';
import * as webServer from './WebServer';
import * as psm from './prettify-symbols-mode';

const opener = require('opener');

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
  return `file://${uri.path}?${uri.query}#${uri.fragment}`;
}

class IFrameDocumentProvider implements vscode.TextDocumentContentProvider {
  private onDidChangeEmitter = new vscode.EventEmitter<vscode.Uri>();

  public provideTextDocumentContent(uri: vscode.Uri): string {
    return `<!DOCTYPE HTML><body style="margin:0px;padding:0px;width:100%;height:100vh;border:none;position:absolute;top:0px;left:0px;right:0px;bottom:0px">
<iframe src="${coqViewToFileUri(uri)}" seamless style="position:absolute;top:0px;left:0px;right:0px;bottom:0px;border:none;margin:0px;padding:0px;width:100%;height:100%" />
</body>`;
  }
  
  public get onDidChange(): vscode.Event<vscode.Uri> {
    return this.onDidChangeEmitter.event;
  }
}

var coqViewProvider : IFrameDocumentProvider|null = null;

/**
 * Displays a Markdown-HTML file which contains javascript to connect to this view
 * and update the goals and show other status info
 */
export class HtmlCoqView implements view.CoqView {
  private docUri: vscode.Uri;
  private server : WebSocket.Server;
  private httpServer : http.Server;
  // private connection : Promise<WebSocket>;
  private serverReady : Promise<void>;
  private currentState : proto.CommandResult = {type: 'not-running', reason: 'not-started'}; 
  private coqViewUri : vscode.Uri;
  private currentSettings : SettingsState = {}; 
  private visible = false;

  private resizeEvent = new vscode.EventEmitter<number>();

  public get resize() : vscode.Event<number> { return this.resizeEvent.event; }
  
  constructor(uri: vscode.Uri, context: vscode.ExtensionContext) {
    if(coqViewProvider===null) {    
      coqViewProvider = new IFrameDocumentProvider();
      var registration = vscode.workspace.registerTextDocumentContentProvider('coq-view', coqViewProvider);
      context.subscriptions.push(registration);
      context.subscriptions.push(vscode.workspace.onDidChangeConfiguration(() => this.updateSettings()))
    }
    
    this.docUri = uri;
    
    const httpServer = this.httpServer = http.createServer();
    this.serverReady = new Promise<void>((resolve, reject) =>
      httpServer.listen(0,'localhost',undefined,(e:any) => {
        if(e)
          reject(e)
        else
          resolve();
      }));
    
    this.server = new WebSocket.Server({server: httpServer});
    this.server.on('connection', (ws: WebSocket) => {
      ws.onmessage = (event) => this.handleClientMessage(event);
      this.updateSettings([ws]);
      this.sendMessage({command: 'goal-update', goal: this.currentState}, [ws]);
    })

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
      await this.serverReady;
      const serverAddress = this.httpServer.address();

      await HtmlCoqView.prepareStyleSheet();
      this.coqViewUri = vscode.Uri.parse(`coq-view://${proofViewHtmlPath().path.replace(/%3A/, ':')}?host=${serverAddress.address}&port=${serverAddress.port}`);
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

  public async show(preserveFocus: boolean, pane: vscode.ViewColumn) {
    if(!this.coqViewUri)
      await this.createBuffer();

    this.visible = true;

    // const focusedDoc = vscode.window.activeTextEditor ? vscode.window.activeTextEditor.document : null;
    await vscode.commands.executeCommand('vscode.previewHtml', this.coqViewUri, pane, "ProofView: " + path.basename(this.docUri.fsPath));
    // if(preserveFocus && focusedDoc)
    //   await vscode.window.showTextDocument(focusedDoc);
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
    // this.editor.hide();
  }

  private async sendMessage(message: ProofViewProtocol, clients = this.server.clients) {
    await this.serverReady;
    if(!clients)
      clients = this.server.clients;
    for(const connection of clients) {
      try {
        connection.send(JSON.stringify(message));
      } catch(error) {}
    }
  }
  
  private async updateClients(state: proto.CommandResult, clients = this.server.clients) {
    this.currentState = state;
    await this.sendMessage({command: 'goal-update', goal: state}, clients);
  }

  public update(state: proto.CommandResult) {
    this.updateClients(state, this.server.clients);
  } 
  

  private async updateSettings(clients = this.server.clients) {
    this.currentSettings.fontFamily = vscode.workspace.getConfiguration("editor").get("fontFamily") as string;
    this.currentSettings.fontSize = `${vscode.workspace.getConfiguration("editor").get("fontSize") as number}px`;
    this.currentSettings.fontWeight = vscode.workspace.getConfiguration("editor").get("fontWeight") as string;
    this.currentSettings.cssFile = decodeURIComponent(proofViewCSSFile().toString());
    this.currentSettings.prettifySymbolsMode = psm.isEnabled();
    await this.sendMessage(Object.assign<SettingsState,{command: 'settings-update'}>(this.currentSettings,{command: 'settings-update'}), clients);
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
