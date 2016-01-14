'use strict';
import { RequestType, NotificationType } from 'vscode-jsonrpc';
import { FailValue } from './coq-proto';

// 
// // import { RequestType, NotificationType, ResponseEror } from 'vscode-jsonrpc';
// import {
// 	createConnection, IConnection, TextDocumentSyncKind,
// 	TextDocuments, ITextDocument, Diagnostic, DiagnosticSeverity,
// 	InitializeParams, InitializeResult, TextDocumentIdentifier,
// 	CompletionItem, CompletionItemKind
// } from 'vscode-languageserver';
// 
// export namespace StepForwardRequest { 
//   export const type: RequestType<void, void, void> = { get method() { return 'coqtop/stepForward'; } }; 
// } 

// The settings interface describe the server relevant settings part
export interface Settings {
	coqtop: CoqTopSettings;
}

// These are the example settings we defined in the client's package.json
// file
export interface CoqTopSettings {
  coqPath: string;
  wrapper: string;
}


export declare interface CoqTopParams {
  uri: string;
}
export declare interface CoqTopStepForwardResult {
  processingStart: number;
  processingEnd: number;
}
export declare interface CoqTopStepBackwardResult {
  commandStart: number;
  commandEnd: number;
}
export interface Goal {
  id: number;
  hypotheses: string[];
  goal: string;
}
export declare interface CoqTopGoalResult {
  goals?: Goal[];
  backgroundGoals?: Goal[],
  shelvedGoals?: Goal[],
  abandonedGoals?: Goal[],
  error?: FailValue;
}
export declare interface CoqTopInterpretToPointParams extends CoqTopParams {
  offset: number;
}


export namespace InterruptCoqRequest { 
  export const type: RequestType<CoqTopParams, void, void> = { method: 'coqtop/interrupt' }; 
} 
export namespace QuitCoqRequest { 
  export const type: RequestType<CoqTopParams, void, void> = { method: 'coqtop/quitCoq' }; 
} 
export namespace ResetCoqRequest { 
  export const type: RequestType<CoqTopParams, void, void> = { method: 'coqtop/resetCoq' }; 
} 
export namespace StepForwardRequest { 
  export const type: RequestType<CoqTopParams, CoqTopGoalResult, void> = { method: 'coqtop/stepForward' }; 
} 
export namespace StepBackwardRequest { 
  export const type: RequestType<CoqTopParams, CoqTopGoalResult, void> = { method: 'coqtop/stepBackward' }; 
} 
export namespace InterpretToPointRequest { 
  export const type: RequestType<CoqTopInterpretToPointParams, CoqTopGoalResult, void> = { method: 'coqtop/interpretToPoint' }; 
} 
export namespace InterpretToEndRequest { 
  export const type: RequestType<CoqTopParams, CoqTopGoalResult, void> = { method: 'coqtop/interpretToEnd' }; 
} 
export namespace GoalRequest { 
  export const type: RequestType<CoqTopParams, CoqTopGoalResult, void> = { method: 'coqtop/goal' }; 
}
export namespace LocateRequest { 
  export const type: RequestType<CoqTopQueryParams, CoqTopQueryResult, void> = { method: 'coqtop/locate' }; 
} 
export declare interface CoqTopQueryParams extends CoqTopParams {
  query: string;
}
export declare interface CoqTopQueryResult {
  searchResults: string;
}


export enum HighlightType {
  Clear,  SyntaxError,  TacticFailure,  Parsing,  Processing, Incomplete, Complete, InProgress, Processed 
}

export interface Highlight {
  style: HighlightType;
  textBegin: number;
  textEnd: number;
  message?: string;
}

export declare interface NotificationParams {
  uri: string;
}

export declare interface NotifyHighlightParams extends NotificationParams {
  highlights : Highlight[];
}

export namespace UpdateHighlightsNotification { 
  export const type: NotificationType<NotifyHighlightParams> = { method: 'coqtop/updateHighlights' }; 
} 

export declare interface NotifyMessageParams extends NotificationParams {
  level: string;
  message: string;
}
export namespace CoqMessageNotification { 
  export const type: NotificationType<NotifyMessageParams> = { method: 'coqtop/message' }; 
} 

export namespace CoqResetNotification { 
  export const type: NotificationType<NotificationParams> = { method: 'coqtop/wasReset' }; 
} 

export interface NotifyStateViewUrlParams extends NotificationParams {
  stateUrl: string;
}

export namespace CoqStateViewUrlNotification { 
  export const type: NotificationType<NotifyStateViewUrlParams> = { method: 'coqtop/stateViewUrl' }; 
} 
