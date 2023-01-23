import { integer, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position } from "vscode";

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
    position: Position;
}

export interface UpdateProofViewResponse {
    goals: Goal[];
    shelvedGoals: Goal[];
    givenUpGoals: Goal[];
}
