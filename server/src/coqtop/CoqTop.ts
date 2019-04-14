'use strict';

import * as net from 'net';
import * as util from 'util';
import * as path from 'path';
import * as events from 'events';
import * as stream from 'stream';
import * as coqXml from './xml-protocol/coq-xml';
import * as vscode from 'vscode-languageserver';

import * as coqProto from './coq-proto';
import {ChildProcess, exec, spawn} from 'child_process';
import {CoqTopSettings, LtacProfTactic, LtacProfResults} from '../protocol';
import * as fs from 'fs';
import * as os from 'os';
import * as xmlTypes from './xml-protocol/CoqXmlProtocolTypes';
import {AnnotatedText, normalizeText, textToDisplayString} from '../util/AnnotatedText';
import {createDeserializer} from './xml-protocol/deserialize';

/** Coqtop was interrupted; call cancelled */
export class Interrupted {
  constructor(
    public stateId: number)
  {}
  public toString() {
    return 'Coqtop Interrupted';
  }
}

/** A fatal error of coqtop */
export class CoqtopSpawnError {
  constructor(private path: string, private message: string)
  {}

  public get binPath() : string {
    return this.path;
  }

  public toString() {
    return "Could not start coqtop: " + this.path + (this.message? "\n" + this.message : "");
  }
}
/** A call did not succeed; a nonfatal error */
export class CallFailure {
  constructor(
    public message: AnnotatedText,
    public stateId?: number,
    public range?: coqProto.Location)
  {
    this.message = normalizeText(this.message);
  }
  public toString() {
    return textToDisplayString(this.message) +
      (this.range || this.stateId
        ? "  (" +
          (this.range ? `offsets ${this.range.start}-${this.range.stop}` : (this.stateId ? " " : "")) +
          (this.stateId ? ` of stateId ${this.stateId}` : "")
          + ")"
        : "")
  }
}

export interface InitResult {
  stateId: number;
}
export interface AddResult {
  stateId: number;
  unfocusedStateId?: number;
  message: AnnotatedText;
}
export interface EditAtFocusResult {
  stateId: number;
  qedStateId: number;
  oldStateIdTip: number;
}
export interface EditAtResult {
  enterFocus?: EditAtFocusResult;
}
export interface ProofView {
  goals: coqProto.Subgoal[];
  backgroundGoals: coqProto.UnfocusedGoalStack
  shelvedGoals: coqProto.Subgoal[];
  abandonedGoals: coqProto.Subgoal[];
}



export type NoProofTag = {mode: 'no-proof'}
export type ProofModeTag = {mode: 'proof'}
export type NoProofResult = NoProofTag & {}
export type ProofModeResult = ProofModeTag & ProofView
export type GoalResult = NoProofResult | ProofModeResult





export interface EventCallbacks {
  onFeedback? : (feedback: coqProto.StateFeedback) => void;
  onMessage? : (msg: coqProto.Message) => void;
  onClosed?: (isError: boolean, message?: string) => void;
}

export function detectVersion(coqtopModule: string, cwd: string, console?: {log: (string)=>void, warn: (string)=>void}) : Promise<string|null> {
  if(console)
    console.log('exec: ' + coqtopModule + ' -v');
  return new Promise<string>((resolve,reject) => {
    try {
      const coqtop = spawn(coqtopModule, ['-v'], {detached: false, cwd: cwd});
      let result = "";

      coqtop.stdout.on('data', (data:string) => {
        result += data
      });

      coqtop.on('close', (code:number) => {
        const ver = /^\s*The Coq Proof Assistant, version (.+?)\s/.exec(result);
        // if(!ver)
        //   console.warn('Could not detect coqtop version');
        resolve(!ver ? undefined : ver[1]);
      });
      coqtop.on('error', (code:number) => {
        // console.warn(`Could not start coqtop; error code: ${code}`)
        reject(new CoqtopSpawnError(coqtopModule, `error code: ${code}`));
      });
    } catch(err) {
      reject(new CoqtopSpawnError(coqtopModule, err));
    }
  })
}

export abstract class IdeSlave {
  protected callbacks : EventCallbacks = {};
  public onFeedback(handler: (feedback: coqProto.StateFeedback) => void) : {dispose: ()=>void}
  {
    this.callbacks.onFeedback = handler;
    return { dispose: () => { this.callbacks.onFeedback = undefined; } }
  }

  public onMessage(handler: (msg: coqProto.Message) => void)
  {
    this.callbacks.onMessage = handler;
    return { dispose: () => { this.callbacks.onMessage = undefined; } }
  }

  public onClosed(handler: (isError: boolean, message?: string) => void)
  {
    this.callbacks.onClosed = handler;
    return { dispose: () => { this.callbacks.onClosed = undefined; } }
  }

  // connect(version: string, mainR: stream.Readable, mainW: stream.Writable, controlR: stream.Readable, controlW: stream.Writable);
  public abstract dispose() : void;
  public abstract isConnected() : boolean;
  public abstract coqInterrupt() : Promise<boolean>;
  public abstract coqInit() : Promise<InitResult>;
  public abstract coqQuit() : Promise<void>;
  public abstract coqGoal() : Promise<GoalResult>;
  public abstract getStatus(force: boolean) : Promise<coqProto.CoqStatus>;
  public abstract coqAddCommand(command: string, editId: number, stateId: number, verbose?: boolean) : Promise<AddResult>;
  public abstract coqEditAt(stateId: number) : Promise<EditAtResult>;
  public abstract coqLtacProfilingResults(stateId?: number, routeId?: number) : Promise<void>;
  public abstract coqResizeWindow(columns: number) : Promise<void>;
  public abstract coqQuery(query: string, stateId?: number, routeId?: number) : Promise<AnnotatedText>;
  public abstract coqGetOptions(options: CoqOptions) : Promise<void>;
  public abstract coqSetOptions(options: CoqOptions) : Promise<void>;
}

export class CommunicationError extends Error {
}

export abstract class CoqTop extends IdeSlave {
  public abstract dispose(): void;
  public abstract isRunning() : boolean;
  public abstract getVersion() : string;
  public abstract startCoq() : Promise<InitResult>;
  // setupCoqTop(wrapper: string|null) : Promise<void>;

  /** Start coqtop.
   * Use two ports: one for reading & one for writing; i.e. HOST:READPORT:WRITEPORT
   */
  // setupCoqTopReadAndWritePorts() : Promise<void>;
  public abstract isConnected() : boolean;
  public abstract coqInterrupt() : Promise<boolean>;
  public abstract coqInit() : Promise<InitResult>;
  public abstract coqQuit() : Promise<void>;
  public abstract coqGoal() : Promise<GoalResult>;
  public abstract getStatus(force: boolean) : Promise<coqProto.CoqStatus>;
  public abstract coqAddCommand(command: string, editId: number, stateId: number, verbose?: boolean) : Promise<AddResult>;
  public abstract coqEditAt(stateId: number) : Promise<EditAtResult>;
  public abstract coqLtacProfilingResults(stateId?: number, routeId?: number) : Promise<void>;
  public abstract coqResizeWindow(columns: number) : Promise<void>;
  public abstract coqQuery(query: string, stateId?: number, routeId?: number) : Promise<AnnotatedText>;
  public abstract coqGetOptions(options: CoqOptions) : Promise<void>;
  public abstract coqSetOptions(options: CoqOptions) : Promise<void>;
}

export interface CoqOptions {
  asymmetricPatterns?: boolean,
  atomicLoad?: boolean,
  automaticCoercionsImport?: boolean,
  automaticIntroduction?: boolean,
  booleanEqualitySchemes?: boolean,
  bracketingLastIntroductionPattern?: boolean,
  bulletBehavior?: string; // enum {Strict,
  subproofsCaseAnalysisSchemes?: boolean,
  compatNotations?: boolean,
  congruenceDepth?: number,
  congruenceVerbose?: boolean,
  contextualImplicit?: boolean,
  debugAuto?: boolean,
  debugEauto?: boolean,
  debugRAKAM?: boolean,
  debugTacticUnification?: boolean,
  debugTrivial?: boolean,
  debugUnification?: boolean,
  decidableEqualitySchemes?: boolean,
  defaultClearingUsedHypotheses?: boolean,
  defaultGoalSelector?: number,
  defaultProofMode?: string; // enum {Classic,
  defaultProofUsing?: any,
  defaultTimeout?: number,
  dependentPropositionsElimination?: boolean,
  discriminateIntroduction?: boolean,
  dumpBytecode?: boolean,
  eliminationSchemes?: boolean,
  equalityScheme?: boolean,
  extractionAutoInline?: boolean,
  extractionConservativeTypes?: boolean,
  extractionFileComment?: string,
  extractionFlag?: number,
  extractionKeepSingleton?: boolean,
  extractionOptimize?: boolean,
  extractionSafeImplicits?: boolean,
  extractionTypeExpand?: boolean,
  firstorderDepth?: number,
  hideObligations?: boolean,
  implicitArguments?: boolean,
  infoAuto?: boolean,
  infoEauto?: boolean,
  infoLevel?: any,
  infoTrivial?: boolean,
  injectionL2RPatternOrder?: boolean,
  injectionOnProofs?: boolean,
  inlineLevel?: number,
  intuitionIffUnfolding?: boolean,
  intuitionNegationUnfolding?: boolean,
  kernelTermSharing?: boolean,
  keyedUnification?: boolean,
  looseHintBehavior?: string; // enum {Lax,
  maximalImplicitInsertion?: boolean,
  nonrecursiveEliminationSchemes?: boolean,
  parsingExplicit?: boolean,
  primitiveProjections?: boolean,
  printingAll?: boolean,
  printingCoercions?: boolean,
  printingDepth?: number,
  printingExistentialInstances?: boolean,
  printingImplicit?: boolean,
  printingImplicitDefensive?: boolean,
  printingMatching?: boolean,
  printingNotations?: boolean,
  printingPrimitiveProjectionCompatibility?: boolean,
  printingPrimitiveProjectionParameters?: boolean,
  printingProjections?: boolean,
  printingRecords?: boolean,
  printingSynth?: boolean,
  printingUniverses?: boolean,
  printingWidth?: number,
  printingWildcard?: boolean,
  programMode?: boolean,
  proofUsingClearUnused?: boolean,
  recordEliminationSchemes?: boolean,
  regularSubstTactic?: boolean,
  reversiblePatternImplicit?: boolean,
  rewritingSchemes?: boolean,
  shortModulePrinting?: boolean,
  shrinkObligations?: boolean,
  simplIsCbn?: boolean,
  standardPropositionEliminationNames?: boolean,
  strictImplicit?: boolean,
  strictProofs?: boolean,
  strictUniverseDeclaration?: boolean,
  stronglyStrictImplicit?: boolean,
  suggestProofUsing?: boolean,
  tacticCompatContext?: boolean,
  tacticEvarsPatternUnification?: boolean,
  transparentObligations?: boolean,
  typeclassResolutionAfterApply?: boolean,
  typeclassResolutionForConversion?: boolean,
  typeclassesDebug?: boolean,
  typeclassesDependencyOrder?: boolean,
  typeclassesDepth?: any,
  typeclassesModuloEta?: boolean,
  typeclassesStrictResolution?: boolean,
  typeclassesUniqueInstances?: boolean,
  typeclassesUniqueSolutions?: boolean,
  universalLemmaUnderConjunction?: boolean,
  universeMinimizationToSet?: boolean,
  universePolymorphism?: boolean,
  verboseCompatNotations?: boolean,
  // Asynchronous options:
  function_debug?: boolean,
  function_raw_tcc?: boolean,
  functionalInductionRewriteDependent?: boolean,
  hypsLimit?: any,
  ltacDebug?: boolean,
  silent?: boolean,
  undo?: any,
  // [DEPRECATED] Tables: Search Blacklist Printing Coercion Printing If Printing Let Printing Record Printing Constructor
  // [DEPRECATED] Extraction AccessOpaque: boolean;
  // [DEPRECATED] Refine Instance Mode: boolean;
  // [DEPRECATED] Tactic Pattern Unification: boolean;
}