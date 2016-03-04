'use strict';
import * as vscode from 'vscode'
import * as fs from 'fs'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'
import * as textUtil from './text-util'
import * as WebSocket from 'ws';
import * as http from 'http';
import * as path from 'path';

const opener = require('opener');

interface ControllerEvent {
  eventName: string;
  params: ResizeEvent // | | | | | ;
}

interface ResizeEvent {
  columns: number;
}

function createFile(path: string) : Promise<number> {
  return new Promise<number>((resolve,reject) => {
    fs.open(path, 'w', (err: any, fd: number) => {
      if(err)
        reject(err)
      else
        resolve(fd);
    } );
  })
}

function writeFile(filename: string, data: any) : Promise<void> {
  return new Promise<void>((resolve,reject) => {
    fs.writeFile(filename, data, {encoding: 'utf8'}, (err: NodeJS.ErrnoException) => {
      if(err)
        reject(err)
      else
        resolve();
    } );
  })
}

function edit(editor: vscode.TextEditor) : Promise<vscode.TextEditorEdit> {
  return new Promise<vscode.TextEditorEdit>((resolve) => {
    editor.edit(resolve);
  });
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

var coqViewProvider : IFrameDocumentProvider = null;

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
  private currentState : proto.CoqTopGoalResult = {}; 
  public onresize: (columns: number) => Thenable<void> = null;
  private coqViewUri : vscode.Uri; 
  
  constructor(uri: vscode.Uri, context: vscode.ExtensionContext) {
    if(coqViewProvider===null) {    
      coqViewProvider = new IFrameDocumentProvider();
      var registration = vscode.workspace.registerTextDocumentContentProvider('coq-view', coqViewProvider);
      context.subscriptions.push(registration);
    }
    
    this.docUri = uri;
    
    const httpServer = this.httpServer = http.createServer();
    this.serverReady = new Promise<void>((resolve, reject) =>
      httpServer.listen(0,'localhost',undefined,(e) => {
        if(e)
          reject(e)
        else
          resolve();
      }));
    
    this.server = new WebSocket.Server({server: httpServer});
    this.server.on('connection', (ws: WebSocket) => {
      ws.onmessage = (event) => this.handleClientMessage(event);
      ws.send(JSON.stringify(this.currentState));
    })

    this.createBuffer();
  }
  
  private handleClientResize(event: ResizeEvent) {
    if(this.onresize)
      this.onresize(event.columns);
  }
  
  private handleClientMessage(event: {data: any; type: string; target: WebSocket}) {
    const message = <ControllerEvent>JSON.parse(event.data);
    switch(message.eventName) {
      case 'resize':
        this.handleClientResize(message.params);
    }
  }
  
  private async createBuffer() : Promise<void> {
    try {
      await this.serverReady;
      const serverAddress = this.httpServer.address();

      const templateFileName = vscode.Uri.file(__dirname + '/HtmlView/Coq.html');
      this.coqViewUri = vscode.Uri.parse(`coq-view://${templateFileName.path.replace(/%3A/, ':')}?host=${serverAddress.address}&port=${serverAddress.port}`);

      await this.show(true);


    } catch(err) {
      vscode.window.showErrorMessage(err.toString());
    }    
  }

  public async show(preserveFocus: boolean) {
    // const focusedDoc = vscode.window.activeTextEditor ? vscode.window.activeTextEditor.document : null;
    const result = await vscode.commands.executeCommand('vscode.previewHtml', this.coqViewUri, vscode.ViewColumn.Two);
    // if(preserveFocus && focusedDoc)
    //   await vscode.window.showTextDocument(focusedDoc);
  }

  public showExternal() : Promise<void> {
    return Promise.resolve(opener(decodeURIComponent(coqViewToFileUri(this.coqViewUri).toString()), {command:"firefox"}));
  }

  dispose() {
    // this.editor.hide();
  }
  
  public async update(state: proto.CoqTopGoalResult) {
    this.currentState = state;
    for(const connection of this.server.clients) {
      try {
      connection.send(JSON.stringify(state));
      } catch(error) {}
    }

  }
  
}