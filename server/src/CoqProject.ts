
import {CoqDocument, DocumentCallbacks, TextDocumentItem} from './document';
import {CoqTopSettings, Settings} from './protocol';
import * as vscode from 'vscode-languageserver';
import * as path from 'path';
import * as fs from 'fs';
import * as readline from 'readline';

const coqProjectFileName = '_CoqProject';


export class CoqProject {
  private coqInstances : { [uri: string] : CoqDocument } = {};
  private currentSettings : Settings;
  private workspaceRoot: string;
  private console: vscode.RemoteConsole;
  private coqProjectWatcher: fs.FSWatcher = null;
  private coqProjectModifiedDate : Date = null;
  private loadingCoqProjectInProcess = false;
  // we independently track the settings contributed by the vscode project settings and _CoqProject
  // so they can be modified seperately
  private settingsCoqTopArgs: string[] = [];
  private coqProjectArgs: string[] = [];
  private ready = {event: Promise.resolve<{}>({}), signal: ()=>{} };
  
  constructor(workspaceRoot: string, console: vscode.RemoteConsole) {
    this.workspaceRoot = workspaceRoot;
    this.console = console;
  }

  public getWorkspaceRoot() : string {
      return this.workspaceRoot;
  }
  
  public lookup(uri: string) : CoqDocument {
    var doc = this.coqInstances[uri];
    if(!doc)
      throw 'unknown document: ' + uri;
    return doc;
  }
  
  private notReady() {
     this.ready.event = new Promise<{}>((resolve) => {
       this.ready.signal = () => {
         this.ready = {event: Promise.resolve<{}>({}), signal: ()=>{} };
         resolve()
        };
     });
  }
  
  public async updateSettings(newSettings: Settings) {
    this.notReady();
    this.settingsCoqTopArgs = newSettings.coqtop.args;
    this.currentSettings = newSettings;
    if(newSettings.coqtop.loadCoqProject) {
      this.watchCoqProject();
      await this.loadCoqProject();
    }
    this.ready.signal();
  }
  
  public async open(textDocument: TextDocumentItem, callbacks: DocumentCallbacks): Promise<CoqDocument> {
    await this.ready.event;
    const doc = new CoqDocument(this.currentSettings.coqtop, textDocument, this.console, callbacks);
    this.coqInstances[doc.uri] = doc;
    return doc;
  }
  
  public close(uri: string) {
    this.lookup(uri)
      .close();
    delete this.coqInstances[uri];
  }
  
  private coqProjectFile() {
    return path.join(this.workspaceRoot, coqProjectFileName);
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
  
  private async loadCoqProject() : Promise<void> {
    if(this.loadingCoqProjectInProcess)
      return;
    this.loadingCoqProjectInProcess = true;
      
    try {
      this.coqProjectArgs = [];
      const stats = await this.getFileStats(this.coqProjectFile());
      this.coqProjectModifiedDate = stats.mtime;
      const projectFile = readline.createInterface({
        input: fs.createReadStream(this.coqProjectFile())
      });
      return await new Promise<void>((resolve,reject) => {
        projectFile
          .on('line', (line:string) => {
            const arg = line.trim();
            if(arg.startsWith('-')) {
              this.coqProjectArgs = this.coqProjectArgs.concat(arg.split(' '));
            }
          })
          .on('close', () => {
            this.console.log('loaded settings from ' + coqProjectFileName);
            this.currentSettings.coqtop.args = this.settingsCoqTopArgs.concat(this.coqProjectArgs);
            resolve();
          })
      });
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