'use strict';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import * as util from 'util';
import {Node} from './coq-xml';
export {Node} from './coq-xml';
import {StateId, EditId, Pair, StateFeedback, LtacProfTactic, LtacProfResults,
  UnionL, UnionR, Union, OptionState, Subgoal, Goals, Location, MessageLevel,
  Message, FailValue, UnfocusedGoalStack, SentenceStatus, FeedbackContent,
  ValueReturn, CoqValue, CoqValueList, UnionCoqValue} from '../coq-proto';
import {AnnotatedText} from '../../util/AnnotatedText';

// export interface TypedNode {
//   $name: string;
//   $text: string;
//   /* attributes */
//   $: { [key:string]:coqProto.CoqValue };
//   /* children */
//   $children : coqProto.CoqValue[];
// }

export namespace Nodes {
  export interface StateIdNode {
    $name: "state_id"
    $: { val: number },
    $children: {}[],
  }
  export interface EditIdNode {
    $name: "edit_id"
    $: { val: number }
    $children: {}[],
  }
  export interface IntNode {
    $name: "int",
    $: { },
    // $text: string
    $children: {[0]: string} & {}[],
  }
  export interface BoolNode {
    $name: "bool",
    $: {val: boolean | "true" | "false"}
    $children: {}[],
  }
  export interface StringNode {
    $name: "string",
    $: { },
    // $text: string
    $children: {[0]: string} & {}[],
  }
  export interface UnitNode {
    $name: "unit",
    $: { },
    $children: {}[],
  }
  export interface PairNode {
    $name: "pair",
    $: { },
    $children: {[0]: CoqValue, [1]: CoqValue} & void[]
  }
  export interface ListNode {
    $name: "list",
    $: { },
    $children: CoqValue[]
  }

  export interface UnionNode {
    $name: "union",
    $: {val: 'in_l'|'in_r'},
    $children: CoqValue[],
  }

  export interface OptionSomeNode {
    $name: "option",
    $: {val: 'some'},
    $children: {[0]: CoqValue} & {}[],
  }

  export interface OptionNoneNode {
    $name: "option",
    $: {val: 'none'},
    $children: {}[],
  }
  export type OptionNode = OptionSomeNode | OptionNoneNode;


  export interface OptionValueIntNode {
    $name: 'option_value',
    $: {val: 'intvalue'},
    option: number|null,
    $children: {[0]: number|null} & {}[],
  }

  export interface OptionValueStringOptNode {
    $name: 'option_value',
    $: {val: 'stringoptvalue'},
    option: string|null,
    $children: {[0]: string|null} & {}[],
  }

  export interface OptionValueBoolNode {
    $name: 'option_value',
    $: {val: 'boolvalue'},
    bool: boolean,
    $children: {[0]: boolean} & {}[],
  }

  export interface OptionValueStringNode {
    $name: 'option_value',
    $: {val: 'stringvalue'},
    $children: {[0]: string} & {}[],
  }
  export type OptionValueNode = OptionValueIntNode | OptionValueStringOptNode | OptionValueBoolNode | OptionValueStringNode;

  export interface FeedbackNode {
    $name: 'feedback' ,
    $: {object: "state"|"edit", route: string},
    $children: {[0]: StateId, [1]: FeedbackContent } & {}[]
  }

  export interface WorkerStatusNode {
    $name: 'feedback_content',
    $kind: "workerstatus", // set for type narrowing
    $: {val: "workerstatus"},
    $children: {[0]: Pair<string,string> } & {}[],
  }
  export interface FileDependencyNode {
    $name: 'feedback_content',
    $kind: "filedependency", // set for type narrowing
    $: {val: "filedependency"},
    $children: {[0]: string|null, [1]: string } & {}[],
  }
  export interface FileLoadedNode {
    $name: 'feedback_content',
    $kind: "fileloaded", // set for type narrowing
    $: {val: "fileloaded"},
    $children: {[0]: string, [1]: string } & {}[],
  }

  export interface GlobReferenceNode {
    $name: 'feedback_content',
    $kind: "globref", // set for type narrowing
    $: {val: "globref"},
    $children: {[0]: Location, [1]: string, [2]: string, [3]: string, [4]: string } & {}[],
  }
  export interface GlobDefinitionNode {
    $name: 'feedback_content',
    $kind: "globdef", // set for type narrowing
    $: {val: "globdef"},
    $children: {[0]: Location, [1]: string, [2]: string, [3]: string } & {}[],
  }
  export interface MessageFeedbackNode {
    $name: 'feedback_content',
    $kind: "message", // set for type narrowing
    $: {val: "message"},
    $children: {[0]: Message} & {}[],
  }
  export interface SentenceStatusAddedAxiomNode {
    $name: 'feedback_content',
    $kind: "addedaxiom", // set for type narrowing
    $: {val: "addedaxiom"},
    $children: {}[],
  }
  export interface ErrorMessageNode {
    $name: 'feedback_content',
    $kind: "errormsg", // set for type narrowing
    $: {val: "errormsg"},
    $children: {[0]: Location, [1]: string } & {}[],
  }
  export interface SentenceStatusProcessedNode {
    $name: 'feedback_content',
    $kind: "processed", // set for type narrowing
    $: {val: "processed"},
    $children: {}[],
  }
  export interface SentenceStatusIncompleteNode {
    $name: 'feedback_content',
    $kind: "incomplete", // set for type narrowing
    $: {val: "incomplete"},
    $children: {}[],
  }
  export interface SentenceStatusCompleteNode {
    $name: 'feedback_content',
    $kind: "complete", // set for type narrowing
    $: {val: "complete"},
    $children: {}[],
  }
  export interface SentenceStatusInProgressNode {
    $name: 'feedback_content',
    $kind: "inprogress", // set for type narrowing
    $: {val: "inprogress"},
    $children: {[0]: number } & {}[],
  }
  export interface SentenceStatusProcessingInNode {
    $name: 'feedback_content',
    $kind: "processingin", // set for type narrowing
    $: {val: "processingin"},
    $children: {[0]: string } & {}[],
  }
  export interface CustomFeeedbackNode {
    $name: 'feedback_content',
    $kind: "custom", // set for type narrowing
    $: {val: "custom"},
    $children: {[0]: Location|null, [1]: string, [2]: any } & {}[],
  }
  export interface LtacProfFeeedbackNode {
    $name: 'feedback_content',
    $kind: "custom", // set for type narrowing
    $: {val: "custom"},
    $children: {[0]: Location|null, [1]: "ltacprof", [2]: LtacProfResults } & {}[],
  }

  export type FeedbackContentNode =
    WorkerStatusNode | FileDependencyNode | FileLoadedNode |
    GlobReferenceNode | GlobDefinitionNode | MessageFeedbackNode | ErrorMessageNode |
    SentenceStatusAddedAxiomNode | SentenceStatusProcessedNode | SentenceStatusIncompleteNode | SentenceStatusCompleteNode | SentenceStatusInProgressNode | SentenceStatusProcessingInNode |
    CustomFeeedbackNode | LtacProfFeeedbackNode;

  export interface LtacProfTacticNode {
    $name: 'ltacprof_tactic',
    $: {name: string, total: string, self: string, num_calls: string, max_total: string }
    $children: LtacProfTactic[],
  }

  export interface LtacProfResultsNode {
    $name: 'ltacprof',
    $: {total_time: string }
    $children: LtacProfTactic[],
  }

  export interface OptionStateNode {
    $name: 'option_state',
    $: { },
    $children: {[0]: boolean, [1]: boolean, [2]: string, [3]: number|string|boolean} & {}[],
  }

  export interface GoalNode {
    $name: 'goal',
    $: { },
    $children: {[0]: number, [1]: AnnotatedText[], [2]: AnnotatedText|null} & {}[]
  }

  export interface GoalsNode {
    $name: 'goals',
    $: { },
    $children: {[0]: Subgoal[]|null, [1]: Pair<Subgoal[],Subgoal[]>[], [2]: Subgoal[]|null, [3]: Subgoal[]|null} & {}[]
  }

  export interface LocationNode {
    $name: 'loc',
    $: {start: string, stop: string},
    $children: {}[],
  }

  export interface MessageLevelNode {
    $name: 'message_level',
    $: {val: string}
    $children: {}[],
  }

  export interface MessageNode {
    $name: 'message',
    $children: {[0]: MessageLevel, [1]: AnnotatedText} & {}[]
    message_level: MessageLevel,
  }

  export interface EvarNode {
    $name: 'evar',
    $: { },
    $children: {[0]: string} & {}[],
  }

  export interface StatusNode {
    $name: 'status',
    $: { },
    $children: {[0]: string[], [1]: string|null, [2]: string[], [3]: number} & {}[],
  }

  export interface CoqObjectNode<T> {
    $name: 'coq_object',
    $: { },
    $children: {[0]: string[], [1]: string[], [2]: T} & {}[],
  }

  export interface CoqInfoNode {
    $name: 'coq_info',
    $: { },
    $children: {[0]: string, [1]: string, [2]: string, [3]: string} & {}[]
  }

  export type TypedNode =
    /** Raw nodes */
    StateIdNode | EditIdNode | IntNode | StringNode | UnitNode | BoolNode |
    PairNode | ListNode | UnionNode |
    OptionNode | OptionValueNode | OptionStateNode |
    GoalNode | GoalsNode |
    LocationNode | MessageLevelNode | MessageNode |
    LtacProfTacticNode | LtacProfResultsNode |
    FeedbackNode | FeedbackContentNode |
    ValueNode;

  export interface FailValueNode {
    $name: 'value',
    $: {val: 'fail', loc_s?: string, loc_e?: string},
    $children: {[0]: StateId, [1]: AnnotatedText} & {}[],
  }


  export function optionIsSome(opt: OptionNode): opt is OptionSomeNode {
    return opt.$.val === 'some';
  }
  export function optValIsInt(opt: OptionValueNode) : opt is OptionValueIntNode {
    return opt.$.val === 'intvalue';
  }
  export function optValIsStringOpt(opt: OptionValueNode) : opt is OptionValueStringOptNode {
    return opt.$.val === 'stringoptvalue';
  }
  export function optValIsBool(opt: OptionValueNode) : opt is OptionValueBoolNode {
    return opt.$.val === 'boolvalue';
  }
  export function optValIsString(opt: OptionValueNode) : opt is OptionValueStringNode {
    return opt.$.val === 'stringvalue';
  }

  export function isInl<X,Y>(value: Union<X,Y>) : value is UnionL<X> {
    return value.tag === 'inl';
  }

  export interface GoodValueNode {
    $name: 'value',
    $: {val: 'good'},
    $children: {[0]: ValueReturn } & {}[],
  }

  export type ValueNode = FailValueNode | GoodValueNode;

  export function isFailValue(value: ValueNode) : value is FailValueNode {
    return value.$.val === 'fail';
  }

  export function isGoodValue(value: ValueNode) : value is GoodValueNode {
    return value.$.val === 'good';
  }

 
}







function check(t:'state_id', r: StateId);
function check(t:'edit_id', r: EditId);
function check(t:'int', r: number);
function check(t:'bool', r: boolean);
function check(t:'string', r: string);
function check(t:'unit', r: {});
function check(t:'pair', r: Pair<CoqValue,CoqValue>);
function check(t:'list', r: CoqValueList);
function check(t:'ltacprof_tactic', r: LtacProfTactic);
function check(t:'ltacprof', r: LtacProfResults);
function check(t:'feedback_content', r: FeedbackContent);
function check(t:'feedback', r: StateFeedback);
function check(t:'union', r: UnionCoqValue);
function check(t:'option', r?: CoqValue);
function check(t:'option_value', r?: number|string|boolean);
function check(t:'option_state', r?: OptionState);
function check(t:'goal', r?: Subgoal);
function check(t:'goals', r?: Goals);
function check(t:'loc', r?: Location );
function check(t:'message_level', r?: MessageLevel );
function check(t:'message', r?: Message );
function check(t:'value', r?: ValueReturn|FailValue );
function check(tag:string, result:CoqValue) : CoqValue {
  return result;
} 

function unreachable(x: never) : never { return x }

export abstract class Deserialize {
  public constructor() {}

  public deserialize(value: Node) : CoqValue {
    return this.doDeserialize(value as any as Nodes.TypedNode);
  }

  private doDeserialize(value: Nodes.TypedNode) : CoqValue {
    switch(value.$name)
    {
      case 'state_id':  
        return check(value.$name, +value.$.val);
      case 'edit_id':  
        return check(value.$name, +value.$.val);
      case 'int':
        return check(value.$name, +value.$children[0]);
      case 'string':
        return check(value.$name, value.$children[0]);
      case 'unit':
        return check(value.$name, {});
      case 'pair':
        return check(value.$name, value.$children);
      case 'list':  
        return check(value.$name, value.$children);
      case 'bool':
        if(typeof value.$.val === 'boolean')
          return check(value.$name, value.$.val);
        else if (value.$.val.toLocaleLowerCase() === 'true')
          return check(value.$name, true);
        else
          return check(value.$name, false);
      case 'union':
        switch(value.$.val) {
          case 'in_l': return check(value.$name, {tag: 'inl', value: value.$children[0]});
          case 'in_r': return check(value.$name, {tag: 'inr', value: value.$children[0]});
        }
        break;
      case 'option':
        return check(value.$name, Nodes.optionIsSome(value) ? value.$children[0] : null)
      case 'option_value': {
        if(Nodes.optValIsInt(value))
          return check(value.$name, value.option);
        else if(Nodes.optValIsStringOpt(value))
          return check(value.$name, value.option);
        else if(Nodes.optValIsBool(value))
          return check(value.$name, value.bool);
        else if(Nodes.optValIsString(value))
          return check(value.$name, value.$children[0]);
        else
          break 
      }
      case 'option_state': {
        return check(value.$name, {
          synchronized: value.$children[0],
          deprecated: value.$children[1],
          name: value.$children[2],
          value: value.$children[3],
        })
      }
      case 'goal':
        return check(value.$name, {
          id: +value.$children[0],
          hypotheses: value.$children[1],
          goal: value.$children[2] || []
        })
      case 'goals': {
        return check(value.$name, {
          goals: value.$children[0] || [],
          backgroundGoals: (value.$children[1] || [])
            .reduce<UnfocusedGoalStack>
              ( (bg, v: Pair<Subgoal[],Subgoal[]>) => ({before: v[0], next: bg, after: v[1] }), null),
          shelvedGoals: value.$children[2] || [],
          abandonedGoals: value.$children[3] || []
        })
      } case 'loc':
        return check(value.$name, {start: +value.$.start, stop: +value.$.stop})
      case 'message_level':
        return check(value.$name, coqProto.MessageLevel[value.$.val]);
      case 'message':
        return check(value.$name, {
          level: value.message_level, 
          message: value.$children[1] || ""
        });
      case 'value':
        if(Nodes.isGoodValue(value))
          return check(value.$name, {status: 'good', result: value.$children[0]})
        else
          return check(value.$name, {
            status: 'fail',
            stateId: value.$children[0],
            message: value.$children[1] || "",
            location: {start: +value.$.loc_s, stop: +value.$.loc_e},
          } as FailValue);
      case 'ltacprof_tactic':
        return check(value.$name, {
          name: value.$.name,
          statistics: {
            total: +value.$.total,
            local: +value.$.self,
            num_calls: +value.$.num_calls,
            max_total: +value.$.max_total},
          tactics: value.$children
        });
      case 'ltacprof':
        return check(value.$name, {
          total_time: +value.$.total_time,
          tactics: value.$children
        });
      case 'feedback_content':
        value.$kind = value.$.val;
        return check(value.$name, this.deserializeFeedbackContent(value as Node));
      case 'feedback': {
        let objectId : coqProto.ObjectId;
        if(value.$['object'] === 'state')
          objectId = {objectKind: "stateid", stateId: +value['state_id']};
        else if(value.$['object'] === 'edit')
          objectId = {objectKind: "editid", editId: +value['edit_id']};
        const result = Object.assign<coqProto.FeedbackBase, coqProto.FeedbackContent>({
          objectId: objectId,
          route: +(value.$.route || "0"),
        }, value.$children[1]) /* TODO: TS 2.1 will equate A&(B|C)=(A&B)|(A&C) so this cast will not be necessary */ as coqProto.StateFeedback;
        return check(value.$name, result);
      }
      default:
        return unreachable(value);
    }
  }

  public deserializeFeedbackContent(value: Node) : FeedbackContent {
    return this.doDeserializeFeedbackContent(value as Nodes.FeedbackContentNode);
  }

  private doDeserializeFeedbackContent(value: Nodes.FeedbackContentNode) : FeedbackContent {
    let result : coqProto.FeedbackContent;
    switch (value.$kind)
    { case 'workerstatus': {
      let statusStr = value.$children[0][1];
      let reSearch = /^(?:proof:[ ]*)(.*)/.exec(statusStr);
      if(reSearch)
        result = {
          feedbackKind: "worker-status",
          id: value.$children[0][0],
          state: coqProto.WorkerState.Proof,
          ident: reSearch[1]
        };
      else
        result = {
          feedbackKind: "worker-status",
          id: value.$children[0][0],
          state: coqProto.WorkerState[statusStr]
        };
      return result;
    } case 'filedependency': {
      let file = value.$children[0] || "";
      let dependency = value.$children[1];
      result = {
        feedbackKind: "file-dependency",
        source: file,
        dependsOn: dependency,
      };
      return result;
    } case 'fileloaded':
      result = {
        feedbackKind: "file-loaded",
        module: value.$children[0],
        filename: value.$children[1]
      };
      return result;
      // (Feedback.GlobRef (loc, filepath, modpath, ident, ty))
      // Feedback.feedback (Feedback.GlobDef (loc, id, secpath, ty))
    case 'globref':
      result = {
        feedbackKind: 'glob-ref',
        location: value.$children[0],
        filePath: value.$children[1],
        modulePath: value.$children[2],
        identity: value.$children[3],
        type: value.$children[4],
      }
console.log("glob-ref: " + util.inspect(result));      
      return result;
    case 'globdef':
      result = {
        feedbackKind: 'glob-def',
        location: value.$children[0],
        identity: value.$children[1],
        secPath: value.$children[2],
        type: value.$children[3],
      }
console.log("glob-def: " + util.inspect(result));
      return result;
    case 'message':
      return {
        feedbackKind: "message",
        level: value.$children[0].level,
        location: value.$children[0].location,
        message: value.$children[0].message,
      };
    case 'errormsg':
      return {
        feedbackKind: "message",
        level: coqProto.MessageLevel.Error,
        location: value.$children[0],
        message: value.$children[1]
      };
    case 'addedaxiom':
    case 'processed':
    case 'incomplete':
    case 'complete':
      result = {
        feedbackKind: 'sentence-status',
        status: SentenceStatus[value.$.val],
        worker: "",
        inProgressDelta: 0,
      }
      return result;
    case 'inprogress': // has worker id
      result = {
        feedbackKind: 'sentence-status',
        status: SentenceStatus[value.$.val],
        worker: "",
        inProgressDelta: value.$children[0],
      }
      return result;
    case 'processingin': // change in the nuber of proofs being worked on
      result = {
        feedbackKind: 'sentence-status',
        status: SentenceStatus[value.$.val],
        worker: value.$children[0],
        inProgressDelta: 0,
      }
      return result;
    case 'custom': {
      if(value.$children[1] === 'ltacprof_results')
        result = Object.assign<{feedbackKind: "ltacprof"},LtacProfResults>(
          {feedbackKind: "ltacprof"}, value.$children[2])
      else        
        result = {
          feedbackKind: "custom",
          location: value.$children[0],
          type: value.$children[1],
          data: value.$children[2],
        };
      return result;
    } default:
      result = {
        feedbackKind: "unknown",
        data: (value as Node),
      };
      return result;
    }
  }
}