import { integer, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position } from "vscode";

type Nullable<T> = T | null;

export interface Hypothesis {
    identifiers: string[];
    type: string;
}

export interface Goal {
    id: integer;
    goal: string;
    hypotheses: Hypothesis[];
}

export interface UpdateProofViewRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Nullable<Position>;
}

interface UpdateProofViewResponseType {
    goals: Goal[];
    shelvedGoals: Goal[];
    givenUpGoals: Goal[];
}

export type UpdateProofViewResponse = Nullable<UpdateProofViewResponseType>;

export interface SearchCoqRequest {
    id: string;
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
}

export interface SearchCoqHandshake {
    id: string;
    result?: boolean;
    error?: any;

}

export interface SearchCoqResult {
    id: string;
    name: string; 
    statement: string;
}

export interface AboutCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
    goalIndex?: number;
}

export type AboutCoqResponse = string;

export interface CheckCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
    goalIndex?: number;
};

export type CheckCoqResponse = string; 

export interface LocateCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
};

export type LocateCoqResponse = string; 

export interface InterpretToPointRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
};