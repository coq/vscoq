'use strict';

import * as util from 'util';
import * as coqXml from './xml-protocol/coq-xml';
import * as vscode from 'vscode-languageserver';

import * as coqProto from './coq-proto';
import * as xmlTypes from './xml-protocol/CoqXmlProtocolTypes';
import {createDeserializer} from './xml-protocol/deserialize';

import * as coqtop from './CoqTop';
import {Interrupted, CallFailure, CommunicationError} from './CoqTop';
import {InitResult, AddResult, EditAtResult, ProofView} from './CoqTop';
import {ProofModeResult, GoalResult} from './CoqTop';

import {timeout} from '../util/Timer';

const QUIT_MESSAGE_TIMEOUT_MS = 1000;

export enum IdeSlaveState {
  Disconnected,
  Connected,
  Error,
  Shutdown,
}

export class InternalError extends Error {
}

class IdeSlaveNotConnectedError extends Error {
  constructor() {
    super("IdeSlave is not connected to coqtop")
  }
}

export class IdeSlave extends coqtop.IdeSlave {
  private mainChannelR : NodeJS.ReadableStream;
  private mainChannelW : NodeJS.WritableStream;
  private controlChannelW : NodeJS.WritableStream;
  private parser : coqXml.XmlStream|null = null;
  private coqResultValueListener : {onValue: (value:coqProto.ValueReturn|coqProto.FailValue) => void, onError: (reason: any)=>void} | null = null;


  protected state = IdeSlaveState.Disconnected;

  protected console: vscode.RemoteConsole;
  protected useInterruptMessage = false;

  constructor(console: vscode.RemoteConsole) {
    super();
    this.console = console;
  }

  protected connect(version: string, mainR: NodeJS.ReadableStream, mainW: NodeJS.WritableStream, controlR: NodeJS.ReadableStream, controlW: NodeJS.WritableStream) {
    this.mainChannelR = mainR;
    this.mainChannelW = mainW;
    this.controlChannelW = controlW;
    this.state = IdeSlaveState.Connected;
  
    const deserializer = createDeserializer(version);
    this.parser = new coqXml.XmlStream(this.mainChannelR, deserializer, {
      onFeedback: (feedback: coqProto.StateFeedback) => this.doOnFeedback(feedback),
      onMessage: (msg: coqProto.Message, routeId: coqProto.RouteId, stateId?: coqProto.StateId) => this.doOnMessage(msg, routeId, stateId),
      onOther: (tag: string, x: any) => this.doOnOther(tag, x),
      onError: (x: any) => this.doOnSerializationError(x)
    });
    this.parser.on('error', err => {
      if(this.coqResultValueListener)
        this.coqResultValueListener.onError(err);
    })
    this.parser.on('response: value', value => {
      if(this.coqResultValueListener)
        this.coqResultValueListener.onValue(value);
    });

    // this.mainChannelR.on('data', (data) => this.onMainChannelR(data));
    // this.controlChannelR.on('data', (data) => this.onControlChannelR(data));

    mainR.setEncoding('utf8');
    if(mainR as any == mainW as any) {
      this.setupChannel(mainR, "main channel", (data) => this.onMainChannelR(data));
    } else {
      this.setupChannel(mainR, "main channel (R)", (data) => this.onMainChannelR(data));
      this.setupChannel(mainR, "main channel (W)");
    }

    controlR.setEncoding('utf8');
    if(controlR as any === controlW as any) {
      this.setupChannel(controlR, "control channel", (data) => this.onControlChannelR(data));
    } else {
      this.setupChannel(controlR, "control channel (R)", (data) => this.onControlChannelR(data));
      this.setupChannel(controlR, "control channel (W)");
    }
  }

  private setupChannel(channel: NodeJS.ReadableStream|NodeJS.WritableStream, name: string, dataHandler?: (string) => void) {
    if (dataHandler)
      channel.on('data', (data:string) => dataHandler(data));
    channel.on('error', (err:any) => this.onCoqTopError(err, name));
  }

  private writeMain(message: string) {
    this.mainChannelW.write(message, 'utf8');
  }


  public dispose() {
    this.callbacks = {};
    this.state = IdeSlaveState.Shutdown;
    // if (this.mainChannelR)
    //   this.mainChannelR.end();
    if (this.mainChannelW)
      this.mainChannelW.end();
    // if (this.controlChannelR)
    //   this.controlChannelR.end();
    if (this.controlChannelW)
      this.controlChannelW.end();

    this.mainChannelR = undefined;
    this.mainChannelW = undefined;
    this.controlChannelW = undefined;
  }

  public isConnected() : boolean {
    return this.state === IdeSlaveState.Connected;
  }
  
  protected onCoqTopError(error: string|{message: string}, channelName: string) : void {
    try {
      const message = typeof error === "string" ? error : error.message;
      if(this.state !== IdeSlaveState.Connected)
        return;

      this.console.error(`Error on ${channelName}: ` + message);
      // if(this.callbacks.onClosed)
      //   this.callbacks.onClosed(true, message);
    } finally {
      this.dispose();      
      this.state = IdeSlaveState.Error;
    }
  }
  
  private onMainChannelR(data: string) {
  }

  private onControlChannelR(data: string) {
    this.console.log('control-channelR: ' + data);
  }

  private doOnFeedback(feedback: coqProto.StateFeedback) {
    if(this.callbacks.onFeedback)
      this.callbacks.onFeedback(feedback);
  }

  private doOnMessage(msg: coqProto.Message, routeId: coqProto.RouteId, stateId: coqProto.StateId) {
    if(this.callbacks.onMessage)
      this.callbacks.onMessage(msg, routeId, stateId);
  }

  private doOnOther(tag: string, x: any) {
      // this.console.log("reponse: " + tag + ": " + util.inspect(x));
  }
  private doOnSerializationError(x: any) {}


  private validateValue(value: coqProto.FailValue, logIdent?: string) : never {
    if(value.message === 'User interrupt.')
      throw new Interrupted(value.stateId);
    else {
      let error = new CallFailure(value.message,value.stateId)
      if(value.location)
        error.range = value.location;
      // this.console.log(`ERROR ${logIdent || ""}: ${value.stateId} --> ${value.error.message} ${value.error.range ? `@ ${value.error.range.start}-${value.error.range.stop}`: ""}`);
      throw error;
    }
  }
  
  /**
   * Note: this needs to be called before this.mainChannelW.write to ensure that the handler for 'response: value'
   * is installed on time
   */
  private coqGetResultOnce(logIdent?: string) : Promise<coqProto.ValueReturn> {
    if(this.coqResultValueListener)
       new InternalError('Multiple handlers are being registered for the same response value from Coqtop.') 
    return new Promise<coqProto.ValueReturn>((resolve,reject) => {
      this.coqResultValueListener = {
        onValue: (value:coqProto.ValueReturn|coqProto.FailValue) => {
          this.coqResultValueListener = null;
          try {
            if(value.status === 'good')
              resolve(value);
            else
              this.validateValue(value,logIdent);
          } catch(error) {
            reject(error);
          }
        },
        onError: err => {
          this.coqResultValueListener = null;
          reject(new CommunicationError(err));
        }
      }
    });
  }

  /** @returns true if an interrupt message was sent via the xml protocol */
  public async coqInterrupt() : Promise<boolean> {
    return false;
  }

  protected async checkState() : Promise<void> {
    if(!this.isConnected())
      throw new IdeSlaveNotConnectedError();
  }

  public async coqInit() : Promise<InitResult> {
    await this.checkState();

    const coqResult = this.coqGetResultOnce('Init');
    this.console.log('--------------------------------');
    this.console.log('Call Init()');
    this.writeMain('<call val="Init"><option val="none"/></call>');

    const value = coqProto.GetValue('Init', await coqResult);
    const result = <InitResult>{stateId: value};
    this.console.log(`Init: () --> ${result.stateId}`);
    return result;
  }

  public async coqQuit() : Promise<void> {
    if(!this.isConnected())
      return;
    
    try {
      const coqResult = this.coqGetResultOnce('Quit');
      this.console.log('--------------------------------');
      this.console.log('Call Quit()');
      this.writeMain('<call val="Quit"><unit/></call>');
      try {
        await timeout(coqResult, QUIT_MESSAGE_TIMEOUT_MS, "timeout")
        this.console.log(`Quit: () --> ()`);
      } catch(err) {
        if(err instanceof CommunicationError)
          this.console.log('Communication error: ' + err.message);
        else
          this.console.log(`Forced Quit (timeout).`);
      }
    } catch(error) {
      this.console.log(`Forced Quit.`);
    } finally {
      this.dispose();
    }
  }

  public async coqGoal() : Promise<GoalResult> {
    await this.checkState();

    const coqResult = this.coqGetResultOnce('Goal');
    this.console.log('--------------------------------');
    this.console.log('Call Goal()');
    this.writeMain('<call val="Goal"><unit/></call>');

    const value = coqProto.GetValue('Goal', await coqResult);
    if(value !== null) {
      const result : ProofView = {
        goals: value.goals,
        backgroundGoals: value.backgroundGoals,
        shelvedGoals: value.shelvedGoals,
        abandonedGoals: value.abandonedGoals
      };
      // this.console.log(`Goal: () --> focused: ${result.goals.length}, unfocused: ${this.countBackgroundGoals(result.backgroundGoals)}, shelved: ${result.shelvedGoals.length}, abandoned: ${result.abandonedGoals.length}`);
      return Object.assign(result, <ProofModeResult>{mode: 'proof'});
    } else {
      // this.console.log(`Goal: () --> No Proof`);
      return <GoalResult>{mode: 'no-proof'};
    }
    // this.console.log(`Goal: -->`);
    // if (result.goals && result.goals.length > 0) {
    //   this.console.log("Current:");
    //   result.goals.forEach((g, i) => this.console.log(`    ${i + 1}:${g.id}= ${g.goal}`));
    // }
    // if (result.backgroundGoals) {
    //   this.console.log("Background: ...");
    //   // result.backgroundGoals.forEach((g, i) => this.console.log(`    ${i + 1}) ${util.inspect(g, false, null)}`));
    // }
    // if (result.shelvedGoals && result.shelvedGoals.length > 0) {
    //   this.console.log("Shelved:");
    //   result.shelvedGoals.forEach((g, i) => this.console.log(`    ${i + 1}) ${util.inspect(g, false, null)}`));
    // }
    // if (result.abandonedGoals && result.abandonedGoals.length > 0) {
    //   this.console.log("Abandoned:");
    //   result.abandonedGoals.forEach((g, i) => this.console.log(`    ${i + 1}) ${util.inspect(g, false, null)}`));
    // }
 }

  public async getStatus(force: boolean) : Promise<coqProto.CoqStatus> {
    await this.checkState();

    const coqResult = this.coqGetResultOnce('Status');
    // const verboseStr = verbose===true ? "true" : "false";
    this.console.log('--------------------------------');
    this.console.log(`Call Status(force: ${force})`);
    this.writeMain(`<call val="Status"><bool val="${force ? "true" : "false"}" /></call>`);

    return coqProto.GetValue('Status', await coqResult);
  }
  
  public async coqAddCommand(command: string, editId: number, stateId: number, verbose?: boolean) : Promise<AddResult> {
    await this.checkState();

    const coqResult = this.coqGetResultOnce('Add');
    // const verboseStr = verbose===true ? "true" : "false";
    const verboseStr = verbose === false ? "false" : "true";
    this.console.log('--------------------------------');
    this.console.log(`Call Add("${command.trim().substr(0, 20) + (command.trim().length > 20 ? "..." : "")}", editId: ${editId}, stateId: ${stateId}, verbose: ${verboseStr})`);
    this.writeMain(`<call val="Add"><pair><pair><string>${coqXml.escapeXml(command)}</string><int>${editId}</int></pair><pair><state_id val="${stateId}"/><bool val="${verboseStr}"/></pair></pair></call>`);

    const value = coqProto.GetValue('Add', await coqResult);
    let result : AddResult = {
      stateId: value.assignedState,
      message: value.message,
      unfocusedStateId: value.nextFocusState,
    };
    if(result.stateId === undefined)
      this.console.log(`UNDEFINED Add: ` + util.inspect(value,false,undefined));
    this.console.log(`Add:  ${stateId} --> ${result.stateId} ${result.unfocusedStateId ? `(unfocus ${result.unfocusedStateId})` : ""} "${result.message || ""}"`);
    return result;
  }

  public async coqEditAt(stateId: number) : Promise<EditAtResult> {
    await this.checkState();

    const coqResult = this.coqGetResultOnce('EditAt');
    this.console.log('--------------------------------');
    this.console.log(`Call EditAt(stateId: ${stateId})`);
    this.writeMain(`<call val="Edit_at"><state_id val="${stateId}"/></call>`);    

    const value = coqProto.GetValue('Edit_at', await coqResult);
    let result : EditAtResult;
    if(value) {
      // Jumping inside another proof; create a new tip
      result = {enterFocus: {
        stateId: value.focusedState,
        qedStateId: value.focusedQedState,
        oldStateIdTip: value.oldFocusedState,
      }};
    } else {
      result = {};
    }
    this.console.log(`EditAt: ${stateId} --> ${result.enterFocus ? `{newTipId: ${result.enterFocus.stateId}, qedId: ${result.enterFocus.qedStateId}, oldId: ${result.enterFocus.oldStateIdTip}}` : "{}"}`);
    return result;
  }


  public async coqLtacProfilingResults(stateId?: number, routeId?: number) : Promise<void> {
    await this.checkState();
    stateId = stateId || 0;
    routeId = routeId || 0;

    const coqResult = this.coqGetResultOnce('Query');
    this.console.log('--------------------------------');
    this.console.log(`Call Query(query: "Show Ltac Profile.", stateId: ${stateId}, routeId: ${routeId})`);
    this.writeMain(`<call val="Query"><pair><route_id val="${routeId}"/><pair><string>Show Ltac Profile.</string><state_id val="${stateId}"/></pair></pair></call>`);    

    coqProto.GetValue('Query',await coqResult);
  }

  public async coqResizeWindow(columns: number) : Promise<void> {
    if(!this.isConnected())
      return;

    const coqResult = this.coqGetResultOnce('SetOptions');
    this.console.log('--------------------------------');
    this.console.log(`Call ResizeWindow(columns: ${columns})`);
    this.writeMain(`<call val="SetOptions"><list><pair><list><string>Printing</string><string>Width</string></list><option_value val="intvalue"><option val="some"><int>${columns}</int></option></option_value></pair></list></call>`);
    coqProto.GetValue('SetOptions',await coqResult);
    this.console.log(`ResizeWindow: ${columns} --> ()`);
  }

  public async coqQuery(query: string, stateId: number, routeId?: number) : Promise<void> {
    this.checkState();
    routeId = routeId || 1;

    const coqResult = this.coqGetResultOnce('Query');
    this.console.log('--------------------------------');
    this.console.log(`Call Query(stateId: ${stateId}, ${routeId!==undefined? "routeId: "+routeId+", ":""}query: ${query})`);
    this.writeMain(`<call val="Query"><pair><route_id val="${routeId}"/><pair><string>${coqXml.escapeXml(query)}</string><state_id val="${stateId}"/></pair></pair></call>`);    

    coqProto.GetValue('Query',await coqResult);
    this.console.log(`Query: ${stateId} --> ...`);
  }


  public async coqGetOptions(options: coqtop.CoqOptions) : Promise<void> {
    this.checkState();

    const coqResult = this.coqGetResultOnce('GetOptions');
    // const coqMessageResult = this.coqGetMessageOnce();
    this.console.log('--------------------------------');
    this.console.log(`Call GetOptions()`);
    this.writeMain(`<call val="GetOptions"><unit/></call>`);

    coqProto.GetValue('GetOptions', await coqResult);
    this.console.log(`GetOptions: () --> ...`);
  }

  public async coqSetOptions(options: coqtop.CoqOptions) : Promise<void> {
    this.checkState();
    let xmlOptions: xmlTypes.ProtocolSimpleType[] = [];
    for(let optionKey in options) {
      const rawOptionsName = CoqOptionsMapping[optionKey];
      const rawOptionsValue = options[optionKey];
      if(rawOptionsValue!==undefined && typeof rawOptionsName === 'string') {
        const optionName = rawOptionsName.split(' ');
        xmlOptions.push(new xmlTypes.Pair(optionName, new xmlTypes.OptionValue(rawOptionsValue)))
      }
    }
    const coqResult = this.coqGetResultOnce('SetOptions');
    // const coqMessageResult = this.coqGetMessageOnce();
    this.console.log('--------------------------------');
    this.console.log(`Call SetOptions(...)`);
    // this.console.log(`Call SetOptions(${xmlTypes.encode(xmlOptions)})`);
    this.writeMain(`<call val="SetOptions">${xmlTypes.encode(xmlOptions)}</call>`);    

    coqProto.GetValue('SetOptions', await coqResult);
    this.console.log(`SetOptions: (...) --> ...`);
  }
}


const CoqOptionsMapping = {
  asymmetricPatterns:                       "Asymmetric Patterns",
  atomicLoad:                               "Atomic Load",
  automaticCoercionsImport:                 "Automatic Coercions Import",
  automaticIntroduction:                    "Automatic Introduction",
  booleanEqualitySchemes:                   "Boolean Equality Schemes",
  bracketingLastIntroductionPattern:        "Bracketing Last Introduction Pattern",
  bulletBehavior:                           "Bullet Behavior",
  subproofsCaseAnalysisSchemes:             "Subproofs Case Analysis Schemes",
  compatNotations:                          "Compat Notations",
  congruenceDepth:                          "Congruence Depth",
  congruenceVerbose:                        "Congruence Verbose",
  contextualImplicit:                       "Contextual Implicit",
  debugAuto:                                "Debug Auto",
  debugEauto:                               "Debug Eauto",
  debugRAKAM:                               "Debug Rakam",
  debugTacticUnification:                   "Debug Tactic Unification",
  debugTrivial:                             "Debug Trivial",
  debugUnification:                         "Debug Unification",
  decidableEqualitySchemes:                 "Decidable Equality Schemes",
  defaultClearingUsedHypotheses:            "Default Clearing Used Hypotheses",
  defaultGoalSelector:                      "Default Goal Selector",
  defaultProofMode:                         "Default Proof Mode",
  defaultProofUsing:                        "Default Proof Using",
  defaultTimeout:                           "Default Timeout",
  dependentPropositionsElimination:         "Dependent Propositions Elimination",
  discriminateIntroduction:                 "Discriminate Introduction",
  dumpBytecode:                             "Dump Bytecode",
  eliminationSchemes:                       "Elimination Schemes",
  equalityScheme:                           "Equality Scheme",
  extractionAutoInline:                     "Extraction Auto Inline",
  extractionConservativeTypes:              "Extraction Conservative Types",
  extractionFileComment:                    "Extraction File Comment",
  extractionFlag:                           "Extraction Flag",
  extractionKeepSingleton:                  "Extraction Keep Singleton",
  extractionOptimize:                       "Extraction Optimize",
  extractionSafeImplicits:                  "Extraction Safe Implicits",
  extractionTypeExpand:                     "Extraction Type Expand",
  firstorderDepth:                          "Firstorder Depth",
  hideObligations:                          "Hide Obligations",
  implicitArguments:                        "Implicit Arguments",
  infoAuto:                                 "Info Auto",
  infoEauto:                                "Info Eauto",
  infoLevel:                                "Info Level",
  infoTrivial:                              "Info Trivial",
  injectionL2RPatternOrder:                 "Injection L2 Rpattern Order",
  injectionOnProofs:                        "Injection On Proofs",
  inlineLevel:                              "Inline Level",
  intuitionIffUnfolding:                    "Intuition Iff Unfolding",
  intuitionNegationUnfolding:               "Intuition Negation Unfolding",
  kernelTermSharing:                        "Kernel Term Sharing",
  keyedUnification:                         "Keyed Unification",
  looseHintBehavior:                        "Loose Hint Behavior",
  maximalImplicitInsertion:                 "Maximal Implicit Insertion",
  nonrecursiveEliminationSchemes:           "Nonrecursive Elimination Schemes",
  parsingExplicit:                          "Parsing Explicit",
  primitiveProjections:                     "Primitive Projections",
  printingAll:                              "Printing All",
  printingCoercions:                        "Printing Coercions",
  printingDepth:                            "Printing Depth",
  printingExistentialInstances:             "Printing Existential Instances",
  printingImplicit:                         "Printing Implicit",
  printingImplicitDefensive:                "Printing Implicit Defensive",
  printingMatching:                         "Printing Matching",
  printingNotations:                        "Printing Notations",
  printingPrimitiveProjectionCompatibility: "Printing Primitive Projection Compatibility",
  printingPrimitiveProjectionParameters:    "Printing Primitive Projection Parameters",
  printingProjections:                      "Printing Projections",
  printingRecords:                          "Printing Records",
  printingSynth:                            "Printing Synth",
  printingUniverses:                        "Printing Universes",
  printingWidth:                            "Printing Width",
  printingWildcard:                         "Printing Wildcard",
  programMode:                              "Program Mode",
  proofUsingClearUnused:                    "Proof Using Clear Unused",
  recordEliminationSchemes:                 "Record Elimination Schemes",
  regularSubstTactic:                       "Regular Subst Tactic",
  reversiblePatternImplicit:                "Reversible Pattern Implicit",
  rewritingSchemes:                         "Rewriting Schemes",
  shortModulePrinting:                      "Short Module Printing",
  shrinkObligations:                        "Shrink Obligations",
  simplIsCbn:                               "Simpl Is Cbn",
  standardPropositionEliminationNames:      "Standard Proposition Elimination Names",
  strictImplicit:                           "Strict Implicit",
  strictProofs:                             "Strict Proofs",
  strictUniverseDeclaration:                "Strict Universe Declaration",
  stronglyStrictImplicit:                   "Strongly Strict Implicit",
  suggestProofUsing:                        "Suggest Proof Using",
  tacticCompatContext:                      "Tactic Compat Context",
  tacticEvarsPatternUnification:            "Tactic Evars Pattern Unification",
  transparentObligations:                   "Transparent Obligations",
  typeclassResolutionAfterApply:            "Typeclass Resolution After Apply",
  typeclassResolutionForConversion:         "Typeclass Resolution For Conversion",
  typeclassesDebug:                         "Typeclasses Debug",
  typeclassesDependencyOrder:               "Typeclasses Dependency Order",
  typeclassesDepth:                         "Typeclasses Depth",
  typeclassesModuloEta:                     "Typeclasses Modulo Eta",
  typeclassesStrictResolution:              "Typeclasses Strict Resolution",
  typeclassesUniqueInstances:               "Typeclasses Unique Instances",
  typeclassesUniqueSolutions:               "Typeclasses Unique Solutions",
  universalLemmaUnderConjunction:           "Universal Lemma Under Conjunction",
  universeMinimizationToSet:                "Universe Minimization To Set",
  universePolymorphism:                     "Universe Polymorphism",
  verboseCompatNotations:                   "Verbose Compat Notations",
  // Asynchronous options:
  // function_debug: boolean;
  // function_raw_tcc: boolean;
  // functionalInductionRewriteDependent: boolean;
  // hypsLimit: any;
  // ltacDebug: boolean;
  // silent: boolean;
  // undo: any
  // [DEPRECATED] Tables: Search Blacklist Printing Coercion Printing If Printing Let Printing Record Printing Constructor
  // [DEPRECATED] Extraction AccessOpaque: boolean;
  // [DEPRECATED] Refine Instance Mode: boolean;
  // [DEPRECATED] Tactic Pattern Unification: boolean;

}
