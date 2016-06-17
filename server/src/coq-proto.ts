'use strict';

export type CoqValue = any;

export interface Pair<X,Y> {
  fst: X; snd: Y
}

export type Union<X,Y> = { inl: X } | { inr: Y }

export enum WorkerState { Idle, Processing, Dead, Proof };
export interface WorkerStatus {
  id: string;
  state: WorkerState;
  ident?: string;
}

export enum SentenceStatus {
  Parsed,ProcessingInput,Processed,InProgress,Incomplete,Complete,
  // NOTE!
  // Coq uses IDs like 'processingin'; the below lets us convert into SentenceStatus
  processingin=ProcessingInput,
  processed=Processed,
  inprogress=InProgress,
  incomplete=Incomplete,
  complete=Complete
}

export interface FailValue {
  message: string;
  location?: Location;
}

export interface Value {
  stateId?: number;
  error?: FailValue;
  value?: any;
  message?: string;
  unfocusedStateId?: number;
}
export interface SentenceFeedback {
  status: SentenceStatus;
  worker: string;
}

export interface StateFeedback {
  stateId : number;
  route : number;
  workerStatus?: WorkerStatus[];
  fileDependencies?: Map<string,string[]>;
  fileLoaded?: FileLoaded;
  sentenceFeedback?: SentenceFeedback;
  error?: ErrorMessage;
}

export interface FileDependency {
  filename: string;
  dependsOn: string;
}

export interface FileLoaded {
  module: string;
  filename: string;
}

export enum MessageLevel {
  Warning, warning=Warning,
  Info, info=Info,
  Notice, notice=Notice,
  Error, error=Error,
  Debug, debug=debug,
}

export interface Message {
  level: MessageLevel;
  message: string;
  rich_message?: any;
}

export interface Location {
  start: number;
  stop: number;
}

export interface ErrorMessage {
  message: string;
  location?: Location;
}
export interface EditFeedback {
  editId: number;
  route: number;
  error?: ErrorMessage;
}

export interface Goal {
  id: number;
  hypotheses: any[];
  goal: any;
}

export interface Goals {
  goals: Goal[];
  backgroundGoals: Goal[],
  shelvedGoals: Goal[],
  abandonedGoals: Goal[],
  error?: FailValue;
};


export interface LtacProfTactic {
  name: string;
  statistics: {total: number; self: number; num_calls: number; max_total: number};
  tactics: LtacProfTactic[]
}
export interface LtacProfResults {
  total_time: number;
  tactics: LtacProfTactic[]
}
