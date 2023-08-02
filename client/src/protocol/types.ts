import { integer, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position, Range, Uri } from "vscode";

type Nullable<T> = T | null;

export enum FeedbackChannel {
    debug, 
    info, 
    notice, 
    ignore
}

export type PpTag = string;

export type BlockType =
  | ["Pp_hbox"]
  | ["Pp_vbox", integer]
  | ["Pp_hvbox", integer]
  | ["Pp_hovbox", integer];

export type PpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_glue", PpString[]]
  | ["Ppcmd_box", BlockType, PpString]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

export interface CoqFeedback {
    range: Range;
    message: string;
    channel: FeedbackChannel;
}

export interface CoqFeedbackNotification {
    uri: Uri; 
    feedback: CoqFeedback[]
}

interface Error {
    code: integer; 
    message: string; 
}

export interface Hypothesis {
    identifiers: string[];
    type: PpString;
}

export interface Goal {
    id: integer;
    goal: PpString;
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
}

export interface SearchCoqError {
    id: string; 
    error: Error; 
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