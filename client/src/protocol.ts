'use strict';
import { RequestType, NotificationType } from 'vscode-jsonrpc';

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

export interface Location {
  start: number;
  stop: number;
}
export interface FailValue {
  message: string;
  location?: Location;
}
export declare interface CoqTopInterpretToPointParams extends CoqTopParams {
  offset: number;
}
export declare interface CoqTopQueryParams extends CoqTopParams {
  query: string;
}
export declare interface CoqTopQueryResult {
  searchResults: string;
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


// Parsing->Processing->Processed->[Incomplete|]
export enum HighlightType {
  Clear,         // 
  SyntaxError,   // 
  TacticFailure, // A tactic has failed
  Parsing,       // Has been sent to Coq
  Processing,    // Has been received by Coq
  Incomplete,    // Not accepted; Ex: a Qed. whose proof has failed
  Complete,      // Acceped: 
  InProgress,    // 
  Processed      // Has been (partially?) checked; syntax seems good, but might still fail...?
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
