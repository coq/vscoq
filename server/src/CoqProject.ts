
import {CoqDocument, DocumentCallbacks, TextDocumentItem} from './document';
import {CoqTopSettings, Settings, DocumentSelector} from './protocol';
import * as vscode from 'vscode-languageserver';
import * as path from 'path';
import * as fs from 'fs';
import * as readline from 'readline';
import {PrettifySymbolsMode} from './util/PrettifySymbols';
import * as nodeAsync from './util/nodejs-async';



const coqProjectFileName = '_CoqProject';


export class CoqProject {
  private coqInstances = new Map<string,CoqDocument>();
  private currentSettings : Settings;
  private workspaceRoot: string;
  private coqProjectWatcher: fs.FSWatcher = null;
  private coqProjectModifiedDate : Date = null;
  private loadingCoqProjectInProcess = false;
  private ready = {event: Promise.resolve<{}>({}), signal: ()=>{} };
  private psm = new PrettifySymbolsMode([]);

  // we independently track the settings contributed by the vscode project settings and _CoqProject
  // so they can be modified seperately
  private settingsCoqTopArgs: string[] = [];
  private coqProjectArgs: string[] = [];
  
  constructor(workspaceRoot: string, public readonly connection: vscode.IConnection) {
    if(workspaceRoot)
      connection.console.log("Loaded project at " + workspaceRoot)
    else
      connection.console.log("Loading project with no root directory")
    this.workspaceRoot = workspaceRoot;
  }

  private get console() : vscode.RemoteConsole {
    return this.connection.console;
  }

  public getWorkspaceRoot() : string {
    return this.workspaceRoot;
  }
  
  public lookup(uri: string) : CoqDocument {
    var doc = this.coqInstances.get(uri);
    if(!doc)
      throw 'unknown document: ' + uri;
    return doc;
  }
  
  /** reset the ready promise */
  private notReady() {
     this.ready.event = new Promise<{}>((resolve) => {
       this.ready.signal = () => {
         this.ready = {event: Promise.resolve<{}>({}), signal: ()=>{} };
         resolve()
        };
     });
  }

  public getPrettifySymbols() : PrettifySymbolsMode {
    return this.psm;
  }
  
  private matchesCoq(selector: DocumentSelector) {
    if(typeof selector === 'string')
      return selector === 'coq';
    else if(selector instanceof Array)
      return selector.some((s) => this.matchesCoq(s));
    else
      return selector.language === 'coq';
  }

  public async updateSettings(newSettings: Settings) {
    this.notReady();
    this.settingsCoqTopArgs = newSettings.coqtop.args;
    this.currentSettings = newSettings;

    this.currentSettings.diagnostics = {
      checkTextSynchronization: true
    }
    
    if(newSettings.coq.loadCoqProject) {
      this.watchCoqProject();
      await this.loadCoqProject();
    }
    if(newSettings.prettifySymbolsMode && newSettings.prettifySymbolsMode.substitutions) {
      for(let entry of newSettings.prettifySymbolsMode.substitutions) {
        if(entry.language && entry.substitutions && this.matchesCoq(entry.language)) {
          this.psm = new PrettifySymbolsMode(entry.substitutions);
          break;
        }
      }
    } else
      this.psm = new PrettifySymbolsMode([]);
    this.ready.signal();
  }
  
  public async open(textDocument: TextDocumentItem, callbacks: DocumentCallbacks): Promise<CoqDocument> {
    await this.ready.event;
    const doc = new CoqDocument(this, textDocument, this.console, callbacks);
    this.coqInstances.set(doc.uri, doc);
    return doc;
  }
  
  public close(uri: string) {
    var doc = this.coqInstances.get(uri);
    this.coqInstances.delete(uri);
    if(doc) {
      doc.close();
    }
  }
  
  private coqProjectFile() {
    if(this.workspaceRoot)
      return path.join(this.workspaceRoot, coqProjectFileName);
    else
      return undefined;
  }

  public shutdown() {
    this.coqInstances.forEach((x) => x.close());
    this.coqInstances.clear();
  }
  
  private async isCoqProjectOutOfDate() {
    try {
      const currentStat = await this.getFileStats(this.coqProjectFile());
      return currentStat.mtime > this.coqProjectModifiedDate;
    } catch(err) {
      return false;
    }
  }
  
  private watchCoqProject() {
    if(this.coqProjectWatcher != null)
      this.coqProjectWatcher.close();
    if(!this.workspaceRoot)
      return;
    this.coqProjectWatcher = fs.watch(this.workspaceRoot, async (event, filename) => {
      var d = (await this.getFileStats(this.coqProjectFile())).mtime;
      switch(event) {
        case 'change':
          if((filename && filename==coqProjectFileName) || await this.isCoqProjectOutOfDate()) {
            this.console.log(coqProjectFileName + ' changed');
            await this.loadCoqProject();
          }
      }
    });
  }

  private stopWatchingCoqProject() {
    if(this.coqProjectWatcher != null)
      this.coqProjectWatcher.close();
    this.coqProjectWatcher = null;
  }
  
  private async getFileStats(path: string) {
    return new Promise<fs.Stats>((resolve,reject) => {
      fs.stat(path, (err, stats) => {
        if(err)
          reject(err);
        else
          resolve(stats);
      });      
    })
  }

  private static parseCoqProject(text: string) : string[] {
    const args : string[] = [];
    const projectArgs : string[] = require('string-argv')(text);
    for(let idx = 0; idx < projectArgs.length; ++idx) {
      const opt = projectArgs[idx]
      if(opt === '-R')
        args.push('-R', projectArgs[++idx], projectArgs[++idx])
      else if(opt === '-I')
        args.push('-I', projectArgs[++idx])
      else if(opt === '-Q')
        args.push('-Q', projectArgs[++idx], projectArgs[++idx])
      else if(opt === '-arg')
        args.push(...require('string-argv')(projectArgs[++idx]))
    }
    return args;
  }

  private async loadCoqProject() : Promise<void> {
    if(!this.workspaceRoot)
      return;

    if(this.loadingCoqProjectInProcess)
      return;
    this.loadingCoqProjectInProcess = true;
      
    try {
      const stats = await this.getFileStats(this.coqProjectFile());
      this.coqProjectModifiedDate = stats.mtime;
      const projectFile = await nodeAsync.fs.readFile(this.coqProjectFile(), 'utf8');
      this.coqProjectArgs = CoqProject.parseCoqProject(projectFile);
      this.currentSettings.coqtop.args = [...this.coqProjectArgs, ...this.settingsCoqTopArgs];
    } catch(err) {
      this.coqProjectModifiedDate = null;
    } finally {
      this.loadingCoqProjectInProcess = false;      
    }
  }
  
  public get settings() {
    return this.currentSettings;
  }
  
}

