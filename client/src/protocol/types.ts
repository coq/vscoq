import { integer, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position, Range, Uri } from "vscode";

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
interface ProofViewNotificationType {
    goals: Goal[];
    shelvedGoals: Goal[];
    givenUpGoals: Goal[];
}

export type ProofViewNotification = Nullable<ProofViewNotificationType>;

export interface UpdateHightlightsNotification {
    uri: Uri; 
    parsedRange: Range[];
    processingRange: Range[];
    processedRange: Range[];
}

export interface MoveCursorNotification {
    uri: Uri; 
    range: Range; 
}

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

export interface PrintCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
};

export type PrintCoqResponse = string; 

export interface DocumentStateRequest {
    textDocument: TextDocumentIdentifier;
}

export interface DocumentStateResponse {
    document: string;
}