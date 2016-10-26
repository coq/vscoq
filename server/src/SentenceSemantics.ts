import * as vscode from 'vscode-languageserver';
import * as project from './CoqProject';
import * as server from './server';
import * as path from 'path';
import * as fs from 'fs';
import * as util from 'util';

export abstract class SentenceSemantics {
  public abstract isEqual(x: SentenceSemantics) : boolean;
}

export class LoadModule implements SentenceSemantics {
  private sourceFile : string = undefined;
  public constructor(
    /** filename of *.vo file */
    private filename: string,
    private module: string,
  ) {
    const file = path.parse(this.filename);
    const source = path.join(file.dir, file.name + ".v");
    fs.exists(source, (fileExists) => {
      if(fileExists)
        this.sourceFile = "file://" + source;
    });
  }

  public getSourceFileName() : string {
    return this.sourceFile;
  }

  public getModuleName() : string {
    return this.module
  }

  public getModuleFileName() : string {
    return this.filename
  }

  public isEqual(x: SentenceSemantics) : boolean {
    return x instanceof LoadModule && x.filename === this.filename;
  }
}

