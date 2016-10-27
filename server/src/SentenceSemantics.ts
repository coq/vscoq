import * as vscode from 'vscode-languageserver';
import * as project from './CoqProject';
import * as server from './server';
import * as parser from './coq-parser';
import * as textUtil from './text-util';
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


export class Definition implements SentenceSemantics {
  public constructor(
    public readonly identifier: string,
    public readonly range: vscode.Range,
  ) {
  }

  public isEqual(x: SentenceSemantics) : boolean {
    return x instanceof Definition && x.identifier === this.identifier;
  }
}

export class Inductive implements SentenceSemantics {
  public constructor(
    public readonly identifier: string,
    public readonly range: vscode.Range,
  ) {
  }

  public isEqual(x: SentenceSemantics) : boolean {
    return x instanceof Inductive && x.identifier === this.identifier;
  }
}


export function parseAst(ast: parser.Sentence, pos: vscode.Position) : SentenceSemantics[] {
  switch(ast.type) {
  case "definition":
    return [new Definition(ast.ident.text, textUtil.rangeTranslateRelative(pos,parser.locationRangeToRange(ast.ident.loc)))]  
  case "inductive":
    return [new Inductive(ast.ident.text, textUtil.rangeTranslateRelative(pos,parser.locationRangeToRange(ast.ident.loc)))]  
  }
  return []
}


function identToSymbol(ident: parser.Identifier, kind: vscode.SymbolKind, pos: vscode.Position) : vscode.SymbolInformation {
  return vscode.SymbolInformation.create(ident.text, vscode.SymbolKind.Variable, textUtil.rangeTranslateRelative(pos,parser.locationRangeToRange(ident.loc)));  
}
export function parseAstForSymbols(ast: parser.Sentence, pos: vscode.Position) : vscode.SymbolInformation[] {
  switch(ast.type) {
  case "definition":
    return [identToSymbol(ast.ident, vscode.SymbolKind.Variable, pos)]  
  case "inductive":
    return [identToSymbol(ast.ident, vscode.SymbolKind.Class, pos)]  
  case "ltacdef":
    return [identToSymbol(ast.ident, vscode.SymbolKind.Function, pos)]  
  }
  return []
}