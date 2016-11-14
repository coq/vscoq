import * as vscode from 'vscode-languageserver';
import * as ast from '../parsing/ast-types';

export enum SymbolKind {
  Definition,
  Class,
  Constructor,
  Module, 
}

export class SymbolDefinition {
  private range: vscode.Range;
  public constructor(
    /** short name used to declare the symbol */
    public readonly name: string,
    /** full name of the symbol, considering its context (within a module, etc.) */
    public readonly fullName: string,
    /** where the symbol was defined */
    definitionRange: vscode.Range,
    /** what kind of symbol is this? */
    public readonly kind: SymbolKind,
  ) {
    this.range = definitionRange;
  }

  public get definitionRange() : vscode.Range {
    return this.range;
  }

  public setRange(range: vscode.Range) {
    this.range = range;
  }
}

export class SymbolDbState {
  private parent: SymbolDbState | null;
  private children: SymbolDbState[];
  private symbols: SymbolDefinition[];

  public lookupIdentifier(ident: string) : SymbolDefinition {
    return undefined;
  }
}


export class SymbolsDb {
  private root: SymbolDbState;
  private currentState: SymbolDbState;

  public processSentenceAst(ast: ast.Sentence) : SymbolDbState {
    return this.currentState;
  }
}

