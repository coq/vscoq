'use strict';

import * as path from 'path';
import * as vscode from 'vscode';
import * as util from 'util';
import * as proto from './protocol';
import * as textUtil from './text-util';
import { RangeSet } from './RangeSet';
import { CoqDocument } from './CoqDocument';

import { workspace, TextEditor, TextEditorEdit, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions } from 'vscode-languageclient';
import * as vscodeClient from 'vscode-languageclient';

function createServerProcess(serverModule: string, debugOptions: string[]): ServerOptions {
  let nodejsPath = workspace.getConfiguration('nodejs')['path'] || '';
  let nodejsCmd = path.join(nodejsPath, 'node');

  // If the extension is launch in debug mode the debug server options are use
  // Otherwise the run options are used
  var args = debugOptions.concat([serverModule]);
  return {
    run: { command: nodejsCmd, args: [serverModule] },
    debug: { command: nodejsCmd, args: debugOptions.concat([serverModule]) }
  }
}

function createServerLocalExtension(serverModule: string, debugOptions: string[]): ServerOptions {
  const options: { run: vscodeClient.NodeModule; debug: vscodeClient.NodeModule } = {
    run: { module: serverModule },
    debug: { module: serverModule, options: { execArgv: debugOptions } }
  }
  return options;
}


export class CoqLanguageServer implements vscode.Disposable {
  private static instance: CoqLanguageServer | null = null;
  private subscriptions: vscode.Disposable[] = [];
  private server: LanguageClient = null;
  private cancelRequest = new vscode.CancellationTokenSource();

  private constructor(context: ExtensionContext) {
    // The server is implemented in node
    let serverModule = context.asAbsolutePath(path.join('server/src', 'server.js'));
    // The debug options for the server
    let debugOptions = ["--nolazy", "--debug=6005"];

    // let serverOptions = createServerProcess(serverModule, debugOptions);
    let serverOptions = createServerLocalExtension(serverModule, debugOptions);

    // Options to control the language client
    let clientOptions: LanguageClientOptions = {
      // Register the server for Coq scripts
      documentSelector: ['coq'],
      synchronize: {
        // Synchronize the setting section 'languageServerExample' to the server
        configurationSection: ['coqtop', 'coq', 'prettifySymbolsMode'],
        // Notify the server about file changes to '.clientrc files contain in the workspace
        fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
      }
    }

    /** TODO: remove this once vscode-languageclient 3.0.0alpha.3 comes out, fixing #106 */
    function startedInDebugMode(): boolean {
      let args = (process as any).execArgv;
      if (args) {
        return args.some((arg) => /^--debug=?/.test(arg) || /^--debug-brk=?/.test(arg));
      };
      return false;
    }

    // Create the language client and start the client.
    this.server = new LanguageClient('Coq Language Server', serverOptions, clientOptions, startedInDebugMode());
    this.server.onReady()
      .then(() => {
        this.server.onNotification(proto.UpdateHighlightsNotification.type, (p) => this.onUpdateHighlightsHandlers.forEach((h) => h(p)));
        this.server.onNotification(proto.CoqMessageNotification.type, (p) => this.onMessageHandlers.forEach((h) => h(p)));
        this.server.onNotification(proto.CoqResetNotification.type, (p) => this.onResetHandlers.forEach((h) => h(p)));
        this.server.onNotification(proto.CoqStmFocusNotification.type, (p) => this.onUpdateCoqStmFocusHandlers.forEach((h) => h(p)));
        this.server.onNotification(proto.CoqLtacProfResultsNotification.type, (p) => this.onLtacProfResultsHandlers.forEach((h) => h(p)));
        console.log("Coq language server ready")
      })
      .catch((reason) => console.log("Coq language server failed to load: " + reason.toString()))

    this.subscriptions.push(this.server.start());
  }

  public static create(context: ExtensionContext): CoqLanguageServer {
    if (!CoqLanguageServer.instance)
      CoqLanguageServer.instance = new CoqLanguageServer(context);
    return CoqLanguageServer.instance;
  }

  public static getInstance(): CoqLanguageServer | null {
    return this.instance;
  }

  public dispose() {
    this.server.stop();
    this.subscriptions.forEach((d) => d.dispose());
    this.cancelRequest.dispose();
    this.subscriptions = [];
  }

  private onUpdateHighlightsHandlers = new Set<(params: proto.NotifyHighlightParams) => void>(); 

  public onUpdateHighlights(listener: (params: proto.NotifyHighlightParams) => void) : vscode.Disposable {
    this.onUpdateHighlightsHandlers.add(listener);
    return { dispose: () => this.onUpdateHighlightsHandlers.delete(listener) }
  }

  private onMessageHandlers = new Set<(params: proto.NotifyMessageParams) => void>(); 
  public onMessage(listener: (params: proto.NotifyMessageParams) => void) {
    this.onMessageHandlers.add(listener);
    return { dispose: () => this.onMessageHandlers.delete(listener) }
  }

  private onResetHandlers = new Set<(params: proto.NotificationParams) => void>(); 
  public onReset(listener: (params: proto.NotificationParams) => void) {
    this.onResetHandlers.add(listener);
    return { dispose: () => this.onResetHandlers.delete(listener) }
  }

  private onUpdateCoqStmFocusHandlers = new Set<(params: proto.DocumentPositionParams) => void>(); 
  public onUpdateCoqStmFocus(listener: (params: proto.DocumentPositionParams) => void) {
    this.onUpdateCoqStmFocusHandlers.add(listener);
    return { dispose: () => this.onUpdateCoqStmFocusHandlers.delete(listener) }
  }

  private onLtacProfResultsHandlers = new Set<(params: proto.NotifyLtacProfResultsParams) => void>(); 
  public onLtacProfResults(listener: (params: proto.NotifyLtacProfResultsParams) => void) {
    this.onLtacProfResultsHandlers.add(listener);
    return { dispose: () => this.onLtacProfResultsHandlers.delete(listener) }
  }

  public async interruptCoq(uri: string) {
    await this.server.onReady();
    this.cancelRequest.dispose();
    this.cancelRequest = new vscode.CancellationTokenSource();
    await this.server.sendRequest(proto.InterruptCoqRequest.type, { uri: uri }, this.cancelRequest.token);
  }

  public async quitCoq(uri: string) {
    await this.server.onReady();
    return await this.server.sendRequest(proto.QuitCoqRequest.type, { uri: uri });
  }

  public async resetCoq(uri: string) {
    await this.server.onReady();
    return await this.server.sendRequest(proto.ResetCoqRequest.type, { uri: uri });
  }

  public async getGoal(uri: string): Promise<proto.CommandResult> {
    await this.server.onReady();
    return await this.server.sendRequest(proto.GoalRequest.type, { uri: uri }, this.cancelRequest.token);
  }

  public async getCachedGoal(uri: string, pos: vscode.Position): Promise<proto.CommandResult> {
    await this.server.onReady();
    return await this.server.sendRequest(proto.CachedGoalRequest.type, { uri: uri, position: pos }, this.cancelRequest.token);
  }

  public async finishComputations(uri: string): Promise<void> {
    await this.server.onReady();
    return await this.server.sendRequest(proto.FinishComputationsRequest.type, { uri: uri }, this.cancelRequest.token);
  }

  public async stepForward(uri: string): Promise<proto.CommandResult> {
    await this.server.onReady();
    return this.server.sendRequest(proto.StepForwardRequest.type, { uri: uri }, this.cancelRequest.token);
  }

  public async stepBackward(uri: string): Promise<proto.CommandResult> {
    await this.server.onReady();
    return this.server.sendRequest(proto.StepBackwardRequest.type, { uri: uri }, this.cancelRequest.token);
  }

  public async interpretToPoint(uri: string, location: number|vscode.Position, synchronous?): Promise<proto.CommandResult> {
    await this.server.onReady();
    const params : proto.CoqTopInterpretToPointParams = {
      uri: uri,
      location: location,
      synchronous: synchronous,
    };
    return this.server.sendRequest(proto.InterpretToPointRequest.type, params, this.cancelRequest.token);
  }

  public async interpretToEnd(uri: string, synchronous: boolean): Promise<proto.CommandResult> {
    await this.server.onReady();
    return this.server.sendRequest(proto.InterpretToEndRequest.type, { uri: uri, synchronous: synchronous }, this.cancelRequest.token);
  }

  public async resizeView(uri: string, columns: number): Promise<void> {
    await this.server.onReady();
    return this.server.sendRequest(proto.ResizeWindowRequest.type, <proto.CoqTopResizeWindowParams>{ uri: uri, columns: columns }, this.cancelRequest.token);
  }

  public async ltacProfGetResults(uri: string, offset?: number): Promise<void> {
    await this.server.onReady();
    return this.server.sendRequest(proto.LtacProfResultsRequest.type, { uri: uri, offset: offset }, this.cancelRequest.token);
  }

  public async getPrefixText(uri: string, pos: vscode.Position, token?: vscode.CancellationToken): Promise<string> {
    await this.server.onReady();
    return this.server.sendRequest(proto.GetSentencePrefixTextRequest.type, { uri: uri, position: pos }, token || this.cancelRequest.token);
  }

  public async query(uri: string, query: "locate"|"check"|"print"|"search"|"about"|"searchAbout", term: string): Promise<proto.CoqTopQueryResult> {
    await this.server.onReady();
    return this.server.sendRequest(proto.QueryRequest.type, <proto.CoqTopQueryParams>{
      uri: uri,
      queryFunction: query,
      query: term
    }, this.cancelRequest.token);
  }

  public async setDisplayOptions(uri: string, options: { item: proto.DisplayOption, value: proto.SetDisplayOption }[]): Promise<void> {
    await this.server.onReady();
    return this.server.sendRequest(proto.SetDisplayOptionsRequest.type, <proto.CoqTopSetDisplayOptionsParams>{
      uri: uri,
      options: options
    }, this.cancelRequest.token);
  }
}


export class CoqDocumentLanguageServer implements vscode.Disposable {
  private server = CoqLanguageServer.getInstance();
  private subscriptions : vscode.Disposable[] = []

  public constructor(
    private uri: string
  ) { }

  public dispose() {
    this.subscriptions.forEach((d) => d.dispose());
  }

  public onUpdateHighlights(listener: (params: proto.Highlights) => void) {
    this.subscriptions.push(this.server.onUpdateHighlights((p: proto.NotifyHighlightParams) => {
      if (p.uri === this.uri)
        listener(p);
    }));
  }

  public onMessage(listener: (params: proto.NotifyMessageParams) => void) {
    this.subscriptions.push(this.server.onMessage((p: proto.NotifyMessageParams) => {
      if (p.uri === this.uri)
        listener(p);
    }));
  }

  public onReset(listener: (params: proto.NotificationParams) => void) {
    this.subscriptions.push(this.server.onReset((p: proto.NotificationParams) => {
      if (p.uri === this.uri)
        listener(p);
    }));
  }

  public onUpdateCoqStmFocus(listener: (params: proto.DocumentPositionParams) => void) {
    this.subscriptions.push(this.server.onUpdateCoqStmFocus((p: proto.DocumentPositionParams) => {
      if (p.uri === this.uri)
        listener(p);
    }));
  }

  public onLtacProfResults(listener: (params: proto.LtacProfResults) => void) {
    this.subscriptions.push(this.server.onLtacProfResults((p: proto.NotifyLtacProfResultsParams) => {
      if (p.uri === this.uri)
        listener(p.results);
    }));
  }

  public async interruptCoq() {
    await this.server.interruptCoq(this.uri);
  }

  public quitCoq() {
    return this.server.quitCoq(this.uri);
  }

  public resetCoq() {
    return this.server.resetCoq(this.uri);
  }

  public getGoal(): Thenable<proto.CommandResult> {
    return this.server.getGoal(this.uri);
  }

  public getCachedGoal(pos: vscode.Position): Thenable<proto.CommandResult> {
    return this.server.getCachedGoal(this.uri, pos);
  }

  public finishComputations(): Thenable<void> {
    return this.server.finishComputations(this.uri);
  }

  public stepForward(): Thenable<proto.CommandResult> {
    return this.server.stepForward(this.uri);
  }

  public stepBackward(): Thenable<proto.CommandResult> {
    return this.server.stepBackward(this.uri);
  }

  public interpretToPoint(offset: number|vscode.Position, synchronous: boolean): Thenable<proto.CommandResult> {
    return this.server.interpretToPoint(this.uri, offset, synchronous);
  }

  public interpretToEnd(synchronous: boolean): Thenable<proto.CommandResult> {
    return this.server.interpretToEnd(this.uri, synchronous);
  }

  public resizeView(columns: number): Thenable<void> {
    return this.server.resizeView(this.uri, columns);
  }

  public ltacProfGetResults(offset?: number): Thenable<void> {
    return this.server.ltacProfGetResults(this.uri, offset);
  }

  public query(query: proto.QueryFunction, term: string): Thenable<proto.CoqTopQueryResult> {
    return this.server.query(this.uri, query, term);
  }

  public setDisplayOptions(options: { item: proto.DisplayOption, value: proto.SetDisplayOption }[]): Thenable<void> {
    return this.server.setDisplayOptions(this.uri, options);
  }

}