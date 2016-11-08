'use strict';
import { RequestType, NotificationType } from 'vscode-jsonrpc';
import * as vscode from 'vscode-languageserver-types';

export interface DocumentFilter {
  language?: string,
  pattern?: string,
  scheme?: string,
}
export type DocumentSelector = string | DocumentFilter | (string | DocumentFilter)[];

/** The substitution settings for a language (or group of languages) */
export interface LanguageEntry {
  /** language(s) to apply these substitutions on */
  language:  DocumentSelector;
  /** substitution rules */
  substitutions: Substitution[];
}

export interface PrettifySymbolsModeSettings {
  substitutions: LanguageEntry[],
}

// The settings interface describe the server relevant settings part
export interface Settings {
  coqtop: CoqTopSettings,
  coq: CoqSettings,
  prettifySymbolsMode?: PrettifySymbolsModeSettings,
}


export interface CoqTopSettings {
  /** Path to coqc and coqtop binaries. @default `""` */
  binPath: string;
  /** On Windows: if `coqtop.wrapper` is not specified or the file does not exist, attempt to automatically find and use a wrapper for coqtop. @default `true` */
  autoUseWrapper: boolean;
  /** The filename of an executable to act as an intermediary between coqtop and this extension. It should support an additional `<call val="Interrupt"><unit/></call>` command to send SIGNIT to coqtop and support HOST:PORT addresses (one port number -- not two). */
  wrapper: string;
  /** A list of arguments to send to coqtop. @default `[]` */
  args: string[];
  /** If using the coqtop-wrapper, instruct it to generate a trace file of its xml-protocol interactions. The trace file will be located adjacent to the Coq script with extension `.coq-trace.xml`. @default `false` */
  traceXmlProtocol: boolean;
}

export interface CoqSettings {
  /** Load settings from _CoqProject (if found at the root of the Code project). @default `true` */
  loadCoqProject: boolean,
  /** Move the editor's cursor position as Coq interactively steps forward/backward a command. @default `true` */
  moveCursorToFocus : boolean,
}

export interface FailValue {
  message: string;
  range?: vscode.Range;
  sentence: vscode.Range;
}

export enum SetDisplayOption {
  On, Off, Toggle
}
export enum DisplayOption {
  ImplicitArguments,
  Coercions,
  RawMatchingExpressions,
  Notations,
  AllBasicLowLevelContents,
  ExistentialVariableInstances,
  UniverseLevels,
  AllLowLevelContents,
}

export interface CoqTopParams {
  uri: string;
}

export interface Substitution {
	ugly: string;        // regular expression describing the text to replace
	pretty: string;      // plain-text symbol to show instead
	pre?: string;        // regular expression guard on text before "ugly"
	post?: string;       // regular expression guard on text after "ugly"
	style?: any;         // stylings to apply to the "pretty" text, if specified, or else the ugly text
}

export type TextDifference = "added";

export interface TextAnnotation {
  /** the relationship this text has to the text of another state */
  diff?: TextDifference,
  /** what to display instead of this text */
  substitution?: string,
  /** the underlying text, possibly with more annotations */
  text: string
}

export interface ScopedText {
  /** A scope identifier */
  scope: string,
  /** Extra stuff */
  attributes?: any,
  /** the underlying text, possibly with more annotations */
  text: AnnotatedText,
}

export type AnnotatedText = string | TextAnnotation | ScopedText | (string | TextAnnotation | ScopedText)[];

export enum HypothesisDifference { None, Changed, New, MovedUp, MovedDown }
export interface Hypothesis {
  identifier: string;
  relation: string;
  expression: AnnotatedText;
  diff: HypothesisDifference;
}
export interface Goal {
  id: number;
  hypotheses: Hypothesis[];
  goal: AnnotatedText;
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
  backgroundGoals?: UnfocusedGoalStack,
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
export type BusyTag = {type: 'busy'}
export type NotRunningResult = NotRunningTag
export type BusyResult = BusyTag
export type NoProofResult = NoProofTag
export type FailureResult = FailValue & FailureTag
export type ProofViewResult = ProofView & ProofViewTag
export type InterruptedResult = CommandInterrupted & InterruptedTag
export type CommandResult =
  NotRunningResult |
  BusyResult |
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
export enum QueryFunction { Check, Print, Search, SearchAbout, Locate}
export interface CoqTopQueryParams extends CoqTopParams {
  queryFunction: QueryFunction;
  query: string;
}
export interface CoqTopQueryResult {
  searchResults: AnnotatedText;
}

export interface CoqTopResizeWindowParams extends CoqTopParams {
  columns: number;
}
export namespace ResizeWindowRequest { 
  export const type: RequestType<CoqTopResizeWindowParams, void, void> =
  { get method() { return 'coqtop/resizeWindow' }
  , _:undefined }; 
} 

export interface CoqTopSetDisplayOptionsParams extends CoqTopParams {
  options: {item: DisplayOption, value: SetDisplayOption}[]
}
export namespace SetDisplayOptionsRequest { 
  export const type: RequestType<CoqTopSetDisplayOptionsParams, void, void> =
  { get method() { return 'coqtop/setDisplayOptions' }
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

export namespace GetSentencePrefixTextRequest { 
  export const type: RequestType<DocumentPositionParams, string, void> =
  { get method() { return 'coqtop/getSentencePrefixText' }
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

export type NotifyHighlightParams = NotificationParams & Highlights;

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

export interface DocumentPositionParams extends NotificationParams {
  position: vscode.Position;
}

export namespace CoqStmFocusNotification { 
  export const type: NotificationType<DocumentPositionParams> =
  { get method() { return 'coqtop/stmFocus' }
  , _:undefined }; 
} 


export enum ComputingStatus {Finished, Computing, Interrupted}
// export interface NotifyComputingStatusParams extends NotificationParams {
//   status: ComputingStatus;
//   computeTimeMS: number;
// }
// export namespace CoqComputingStatusNotification { 
//   export const type: NotificationType<NotifyComputingStatusParams> =
//   { get method() { return 'coqtop/computingStatus' }
//   , _:undefined }; 
// } 

export interface NotifyLtacProfResultsParams extends NotificationParams {
  results: LtacProfResults
}
export namespace CoqLtacProfResultsNotification { 
  export const type: NotificationType<NotifyLtacProfResultsParams> =
  { get method() { return 'coqtop/ltacProfResults' }
  , _:undefined }; 
} 
