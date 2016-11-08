import * as fs from 'fs';
import * as path from 'path';
import * as zlib from 'zlib';
import * as http from 'http';
import * as WebSocket from 'ws';

import * as vscode from 'vscode';

export interface GotoOptions {
  /** anchor to make visible */
  anchor: string,
  /** optionally set the background color of `anchor` to `highlight` */
  highlight?: string,
}

interface SetSrcDocMessage {
  type: "set-srcdoc",
  sourceHtml: string,
  goto?: GotoOptions,
}

interface SetSrcMessage {
  type: "set-src",
  uri: string,
  goto?: GotoOptions,
}

interface GotoMessage {
  type: "goto",
  goto?: GotoOptions,
}

interface DataMessage<M> {
  type: "data",
  data: M,
}

interface EvalMessage {
  type: "eval",
  code: string,
}

interface ResultMessage {
  type: "result",
  result: any,
  callId: number,
}

type SendMessageProtocol<M> = SetSrcDocMessage | SetSrcMessage | EvalMessage | GotoMessage | DataMessage<M>;
type RecvMessageProtocol<M> = ResultMessage | DataMessage<M>;


export abstract class WebDocumentProvider<MS,MR> implements vscode.TextDocumentContentProvider {
  private readonly onDidChangeEmitter = new vscode.EventEmitter<vscode.Uri>();
  private readonly httpServer : http.Server;
  private readonly serverReady : Promise<void>;
  private readonly server : WebSocket.Server;
  private onDataHandler : (data: MR) => void;
  private evalResults = new Map<WebSocket,Map<number,{resolve: (x:any) => void, reject: (err:any) => void}>>();
  private nextEvalId = 0;
  private currentAnchor : GotoOptions;

  public constructor() {
    this.httpServer = http.createServer();
    this.serverReady = new Promise<void>((resolve, reject) =>
      this.httpServer.listen(0,'localhost',undefined,(e) => {
        if(e)
          reject(e)
        else
          resolve();
      }));
    this.server = new WebSocket.Server({server: this.httpServer});
    this.server.on('connection', (ws: WebSocket) => {
      this.evalResults.set(ws, new Map())
      ws.onclose = (event) => {
        this.cancelPromises(event.reason, this.evalResults.get(ws).values());
        this.evalResults.delete(ws);
      }
      ws.onmessage = (event) => {
        const message = JSON.parse(event.data) as RecvMessageProtocol<MR>;
        if(message.type === "data")
          this.onData(ws, message.data);
        else if(message.type === "result") {
          const promises = this.evalResults.get(ws);
          const promise = promises.get(message.callId);
          if(promise) {
            promises.delete(message.callId);
            promise.resolve(message.result);
          }
        }
      };
      if(this.currentAnchor)
        this.sendMessage({type: "goto", goto: this.currentAnchor}, [ws]);
      this.onConnection(ws);
    })
  }

  private cancelPromises(reason: any, promises: Iterable<{resolve: (x:any) => void, reject: (err:any) => void}>) {
    for(let promise of promises)
      promise.reject(reason);
  }

  private sendMessageToClient(message: SendMessageProtocol<MS>, callId, client: WebSocket, token?: vscode.CancellationToken) {
    try {
      if(client.readyState !== client.OPEN)
        return Promise.resolve(undefined);
      client.send(JSON.stringify(message));
      const promises = this.evalResults.get(client);
      return new Promise<any>((resolve,reject) => {
        promises.set(callId,{resolve:resolve,reject:reject});
        if(token)
          token.onCancellationRequested((e) => {
            promises.delete(callId);
            reject(e);
          });
      });
    } catch(err) {
      return Promise.reject(err);
    }
  }

  private async sendMessage(message: SendMessageProtocol<MS>, clients = this.server.clients, token?: vscode.CancellationToken) : Promise<MR[]> {
    await this.serverReady;
    const evalId = this.nextEvalId++;
    message['callId'] = evalId;
    if(!clients)
      clients = this.server.clients;
    return await Promise.all(clients.map((connection) => this.sendMessageToClient(message,evalId,connection,token)));
  }

  protected async send(data: MS, clients = this.server.clients) {
    await this.sendMessage({type: "data", data: data}, clients);
  }

  protected async setSourceHTML(htmlSource: string, clients = this.server.clients, options: {goto?: GotoOptions} = {}) {
    this.currentAnchor = options.goto;
    const anchor = options.goto ? options.goto.anchor : undefined;
    const highlight = options.goto ? options.goto.highlight : undefined;
    await this.sendMessage({type: "set-srcdoc", sourceHtml: htmlSource, goto: options.goto}, clients);
  }

  protected async setSourceUri(uri: vscode.Uri, clients = this.server.clients, options: {goto?: {anchor: string, highlight?: string}}) {
    this.currentAnchor = options.goto;
    const anchor = options.goto ? options.goto.anchor : undefined;
    const highlight = options.goto ? options.goto.highlight : undefined;
    await this.sendMessage({type: "set-src", uri: uri.toString(), goto: options.goto}, clients);
  }

  protected async eval(code: string, clients = this.server.clients, token?: vscode.CancellationToken) : Promise<any> {
    return await this.sendMessage({type: "eval", code: code}, clients);
  }

  protected get clients() : WebSocket[] {
    return this.server.clients;
  }

  protected async goto(anchor: string, highlight?: string, clients = this.server.clients) : Promise<void> {
    this.currentAnchor = {anchor: anchor, highlight: highlight};
    await this.sendMessage({type: "goto", goto: this.currentAnchor}, clients);
  }

  protected abstract onConnection(client: WebSocket) : void;

  protected abstract onData(client: WebSocket, data: MR);

  protected abstract provideSource(uri: vscode.Uri, token: vscode.CancellationToken) : Promise<string|vscode.Uri|undefined>;

  public async provideTextDocumentContent(uri: vscode.Uri, token: vscode.CancellationToken): Promise<string> {
    await this.serverReady;
    const {address: address, port: port} = this.httpServer.address();
    const source = await this.provideSource(uri,token);
    let ifattr = "";
    if(source instanceof vscode.Uri)
      ifattr = `src="${source.toString()}"`;
    else if(typeof source === 'string')
      ifattr = `srcdoc="${source}"`;

    const WEB_SOCKET_ADDRESS = `ws://${address}:${port}`;
    return `<!DOCTYPE HTML>
<head>
<script type="text/javascript">
let observer = new MutationObserver(function(mutations) {
    let host = document.getElementById("host");
    const doc = host.contentWindow.document;
    applyStyles(doc);
  });

window.addEventListener('message', function(event) {
  connection.send(JSON.stringify({type:"data", data: event.data}))
}, false);

let simulateAnchor = document.createElement('a');
simulateAnchor.style.display = 'none';


let connection = null;

function load() {
  if(connection)
    connection.close();

  let host = document.getElementById("host");
  connection = new WebSocket("${WEB_SOCKET_ADDRESS}");
  connection.onmessage = function (event) {
    message = JSON.parse(event.data);
    if(!host)
      return;
    if(message.type === 'set-srcdoc') {
      host.onload = function() {
        initializeDoc(host.contentWindow.document, message.goto);
        connection.send(JSON.stringify({type:"result", result: undefined, callId: message.callId}));
      }
      host.srcdoc = message.sourceHtml;
    } else if(message.type === 'set-src') {
      host.onload = function() {
        initializeDoc(host.contentWindow.document, message.goto);
        connection.send(JSON.stringify({type:"result", result: undefined, callId: message.callId}));
      }
      host.src = message.uri;
    } else if(message.type === 'goto') {
      gotoAnchor(host.contentWindow.document, message.goto);  
      connection.send(JSON.stringify({type:"result", result: undefined, callId: message.callId}));
    } else if(message.type === 'data') {
      host.contentWindow.postMessage(message.data, "*");
      connection.send(JSON.stringify({type:"result", result: undefined, callId: message.callId}));
    } else if(message.type === 'eval') {
      const result = host.contentWindow.eval(message.code);
      connection.send(JSON.stringify({type:"result", result: result, callId: message.callId}));
    }
  }
  connection.onclose = function (event) {
    connection = null;
  }

  observer.disconnect();
  observer.observe(document.body, { attributes : true, attributeFilter: ['class'] });
  document.body.appendChild(simulateAnchor);

  initializeDoc(host.contentWindow.document, undefined);
}
let clickEvent = new MouseEvent('click', {view: window, bubbles: true, cancelable: true});
function initializeDoc(doc, goto) {
  applyStyles(doc);
  if(goto)
    gotoAnchor(doc, goto);  
}

function gotoAnchor(doc, goto) {
  if(!goto)
    return;
  const elem = doc.getElementById(goto.anchor);
  if(!elem)
    return;
  elem.scrollIntoView();
  if(goto.highlight)
    elem.style.backgroundColor = goto.highlight;
}
function unload() {
  console.log("UNloading");
}
function applyStyles(doc) {
  var styleSheets = document.styleSheets;
  var cssString = "";
  for (var i = 0, count = styleSheets.length; i < count; ++i) {
    if (styleSheets[i].cssRules) {
      var cssRules = styleSheets[i].cssRules;
      for (var j = 0, countJ = cssRules.length; j < countJ; ++j)
        cssString += cssRules[j].cssText;
    }
    else
      cssString += styleSheets[i].cssText;  // IE8 and earlier
  }
  var style = doc.createElement("style");
  style.type = "text/css";
  style.innerHTML = cssString;
  doc.getElementsByTagName("head")[0].appendChild(style);
  doc.body.classList.add(...document.body.classList);
}
</script>
</head>
<body onload="load()" style="margin:0px;padding:0px;width:100%;height:100vh;border:none;position:absolute;top:0px;left:0px;right:0px;bottom:0px">
<iframe id="host" seamless style="position:absolute;top:0px;left:0px;right:0px;bottom:0px;border:none;margin:0px;padding:0px;width:100%;height:100%" ${ifattr} />
</body>`;
  }
  
  public get onDidChange(): vscode.Event<vscode.Uri> {
    return this.onDidChangeEmitter.event;
  }
}
