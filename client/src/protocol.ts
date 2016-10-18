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
    sentence: vscode.Range;
  }


  export interface CoqTopParams {
    uri: string;
  }
  // export interface CoqTopStepForwardResult {
  //   processingStart: number;
  //   processingEnd: number;
  // }
  // export interface CoqTopStepBackwardResult {
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
    goal: string|{string:string};
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
  export interface ProofView {
    goals: Goal[];
    backgroundGoals: UnfocusedGoalStack,
    shelvedGoals: Goal[],
    abandonedGoals: Goal[],
  }

  export interface CommandInterrupted {
    range: vscode.Range
  }

  export type FocusPosition = {focus: vscode.Position}
  export type NotRunningTag = {type: 'not-running'}
  export type NoProofTag = {type: 'no-proof'}
  export type FailureTag = {type: 'failure'}
  export type ProofViewTag = {type: 'proof-view'}
  export type InterruptedTag = {type: 'interrupted'}
  export type NotRunningResult = NotRunningTag
  export type NoProofResult = NoProofTag
  export type FailureResult = FailValue & FailureTag
  export type ProofViewResult = ProofView & ProofViewTag
  export type InterruptedResult = CommandInterrupted & InterruptedTag
  export type CommandResult =
    NotRunningResult |
    (FailureResult & FocusPosition) |
    (ProofViewResult & FocusPosition) |
    (InterruptedResult & FocusPosition) |
    (NoProofResult & FocusPosition);



  export interface CoqTopInterpretToPointParams extends CoqTopParams {
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
    export const type: RequestType<CoqTopParams, void, void> =
    { get method() { return 'coqtop/interrupt' }
    , _: undefined
    }
  } 
  export namespace QuitCoqRequest { 
    export const type: RequestType<CoqTopParams, void, void> =
    { get method() { return 'coqtop/quitCoq' }
    , _:undefined }; 
  } 
  export namespace ResetCoqRequest { 
    export const type: RequestType<CoqTopParams, void, void> = 
    { get method() { return 'coqtop/resetCoq' }
    , _:undefined }; 
  } 
  export namespace StepForwardRequest { 
    export const type: RequestType<CoqTopParams, CommandResult, void> = 
    { get method() { return 'coqtop/stepForward' }
    , _:undefined }; 
  } 
  export namespace StepBackwardRequest { 
    export const type: RequestType<CoqTopParams, CommandResult, void> = 
    { get method() { return 'coqtop/stepBackward' }
    , _:undefined }; 
  } 
  export namespace InterpretToPointRequest { 
    export const type: RequestType<CoqTopInterpretToPointParams, CommandResult, void> = 
    { get method() { return 'coqtop/interpretToPoint' }
    , _:undefined }; 
  } 
  export namespace InterpretToEndRequest { 
    export const type: RequestType<CoqTopParams, CommandResult, void> = 
    { get method() { return 'coqtop/interpretToEnd' }
    , _:undefined }; 
  } 
  export namespace GoalRequest { 
    export const type: RequestType<CoqTopParams, CommandResult, void> = 
    { get method() { return 'coqtop/goal' }
    , _:undefined }; 
  }
  export namespace QueryRequest { 
    export const type: RequestType<CoqTopQueryParams, CoqTopQueryResult, void> = 
    { get method() { return 'coqtop/query' }
    , _:undefined }; 
  }
  export enum QueryFunction { Check, Search, SearchAbout, Locate}
  export interface CoqTopQueryParams extends CoqTopParams {
    queryFunction: QueryFunction;
    query: string;
  }
  export interface CoqTopQueryResult {
    searchResults: string;
  }

  export interface CoqTopResizeWindowParams extends CoqTopParams {
    columns: number;
  }
  export namespace ResizeWindowRequest { 
    export const type: RequestType<CoqTopResizeWindowParams, void, void> =
    { get method() { return 'coqtop/resizeWindow' }
    , _:undefined }; 
  } 


  export interface CoqTopLtacProfResultsParams extends CoqTopParams {
    offset?: number;
  }
  export namespace LtacProfResultsRequest { 
    export const type: RequestType<CoqTopLtacProfResultsParams, void, void> =
    { get method() { return 'coqtop/ltacProfResults' }
    , _:undefined }; 
  }


  export enum HighlightType {
    StateError=0, Parsing=1, Processing=2, Incomplete=3, Complete=4, InProgress=5, Processed=6 
  }

  // export interface Highlight {
  //   style: HighlightType;
  //   range: vscode.Range;
  // }

  export interface NotificationParams {
    uri: string;
  }

  export interface Highlights {
    ranges: [vscode.Range[],vscode.Range[],vscode.Range[],vscode.Range[],vscode.Range[],vscode.Range[],vscode.Range[]];
  }

  type NotifyHighlightParams = NotificationParams & Highlights;

  export namespace UpdateHighlightsNotification { 
    export const type: NotificationType<NotifyHighlightParams> =
    { get method() { return 'coqtop/updateHighlights' }
    , _:undefined }; 
  } 

  export interface NotifyMessageParams extends NotificationParams {
    level: string;
    message: string;
    rich_message?: any;
  }
  export namespace CoqMessageNotification { 
    export const type: NotificationType<NotifyMessageParams> =
    { get method() { return 'coqtop/message' }
    , _:undefined }; 
  } 

  export namespace CoqResetNotification { 
    export const type: NotificationType<NotificationParams> =
    { get method() { return 'coqtop/wasReset' }
    , _:undefined }; 
  } 

  export interface NotifyCoqStmFocusParams extends NotificationParams {
    focus?: vscode.Position;
  }

  export namespace CoqStmFocusNotification { 
    export const type: NotificationType<NotifyCoqStmFocusParams> =
    { get method() { return 'coqtop/stmFocus' }
    , _:undefined }; 
  } 


  export enum ComputingStatus {Finished, Computing, Interrupted}
  export interface NotifyComputingStatusParams extends NotificationParams {
    status: ComputingStatus;
    computeTimeMS: number;
  }
  export namespace CoqComputingStatusNotification { 
    export const type: NotificationType<NotifyComputingStatusParams> =
    { get method() { return 'coqtop/computingStatus' }
    , _:undefined }; 
  } 

  export interface NotifyLtacProfResultsParams extends NotificationParams {
    results: LtacProfResults
  }
  export namespace CoqLtacProfResultsNotification { 
    export const type: NotificationType<NotifyLtacProfResultsParams> =
    { get method() { return 'coqtop/ltacProfResults' }
    , _:undefined }; 
  } 
