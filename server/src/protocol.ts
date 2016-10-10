'use strict';
import { RequestType, NotificationType } from 'vscode-jsonrpc';
import * as vscode from 'vscode-languageserver-types';

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
  args: string[];
  loadCoqProject: boolean;
}

export interface FailValue {
  message: string;
  range?: vscode.Range;
}


export declare interface CoqTopParams {
  uri: string;
}
// export declare interface CoqTopStepForwardResult {
//   processingStart: number;
//   processingEnd: number;
// }
// export declare interface CoqTopStepBackwardResult {
//   commandStart: number;
//   commandEnd: number;
// }
export enum HypothesisDifference { None, Changed, New, MovedUp, MovedDown }
export enum TextDifference { None, Added, Removed }
export interface TextPartDifference {
  text: string;
  change: TextDifference;
}
export interface Hypothesis {
  identifier: string;
  relation: string;
  expression: string;
  diffExpression?: TextPartDifference[];
  diff: HypothesisDifference;
}
export interface Goal {
  id: number;
  hypotheses: Hypothesis[];
  goal: any;
  diffGoal?: TextPartDifference[];  
}
export interface UnfocusedGoalStack {
  // subgoals that appear before the focus
  before: Goal[];
  // reference to the more-focused background goals
  next?: UnfocusedGoalStack 
  // subgoals that appear after the focus
  after: Goal[];
}
export declare interface CoqTopGoalResult {
  goals?: Goal[];
  backgroundGoals?: UnfocusedGoalStack,
  shelvedGoals?: Goal[],
  abandonedGoals?: Goal[],
  error?: FailValue,
  focus?: vscode.Position
}
export declare interface CoqTopInterpretToPointParams extends CoqTopParams {
  offset: number;
}

export interface LtacProfTactic {
  name: string,
  statistics: {total: number; self: number; num_calls: number; max_total: number},
  tactics: LtacProfTactic[]
}
export interface LtacProfResults {
  total_time: number,
  tactics: LtacProfTactic[]
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
export namespace QueryRequest { 
  export const type: RequestType<CoqTopQueryParams, CoqTopQueryResult, void> = { method: 'coqtop/query' }; 
}
export enum QueryFunction { Check, Search, SearchAbout, Locate}
export declare interface CoqTopQueryParams extends CoqTopParams {
  queryFunction: QueryFunction;
  query: string;
}
export declare interface CoqTopQueryResult {
  searchResults: string;
}

export interface CoqTopResizeWindowParams extends CoqTopParams {
  columns: number;
}
export namespace ResizeWindowRequest { 
  export const type: RequestType<CoqTopResizeWindowParams, void, void> = { method: 'coqtop/resizeWindow' }; 
} 


export interface CoqTopLtacProfResultsParams extends CoqTopParams {
  offset?: number;
}
export namespace LtacProfResultsRequest { 
  export const type: RequestType<CoqTopLtacProfResultsParams, LtacProfResults, void> = { method: 'coqtop/ltacProfResults' }; 
}


export enum HighlightType {
  Clear,  SyntaxError,  TacticFailure,  Parsing,  Processing, Incomplete, Complete, InProgress, Processed 
}

export interface Highlight {
  style: HighlightType;
  range: vscode.Range;
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
  rich_message?: any;
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


export enum ComputingStatus {Finished, Computing, Interrupted}
export declare interface NotifyComputingStatusParams extends NotificationParams {
  status: ComputingStatus;
  computeTimeMS: number;
}
export namespace CoqComputingStatusNotification { 
  export const type: NotificationType<NotifyComputingStatusParams> = { method: 'coqtop/computingStatus' }; 
} 

export declare interface NotifyLtacProfResultsParams extends NotificationParams {
  results: LtacProfResults
}
export namespace CoqLtacProfResultsNotification { 
  export const type: NotificationType<NotifyLtacProfResultsParams> = { method: 'coqtop/ltacProfResults' }; 
} 
