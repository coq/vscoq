'use strict';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import * as util from 'util';
import {Node} from './coq-xml';
export {Node} from './coq-xml';

export abstract class Deserialize {
  public constructor() {}

  public deserialize(value: Node) : coqProto.CoqValue {
    return toCoqValue(value);
  }
}

function toCoqValue(value: Node) : coqProto.CoqValue {
  switch(value.$name)
  {
    case 'state_id':  
      return <number>+value.$['val'];
    case 'edit_id':  
      return <number>+value.$['val'];
    case 'int':
      return <number>+value.$text;
    case 'string':
      return value.$text;
    case 'unit':
      return {};
    case 'pair':
      return <coqProto.Pair<any,any>>{fst: value.$children[0], snd: value.$children[1]};
    case 'list':  
      return value.$children;
    case 'ltacprof_tactic':
      return <coqProto.LtacProfTactic>{
        name: value.$['name'],
        statistics: {
          total: +value.$['total'],
          local: +value.$['self'],
          num_calls: +value.$['num_calls'],
          max_total: +value.$['max_total']},
        tactics: value.$children };
    case 'ltacprof':
      return <coqProto.LtacProfResults>{
        total_time: +value.$['total_time'],
        tactics: value.$children };
    case 'bool':
      let val = value.$['val'];
      if(typeof val === 'boolean')
        return val;
      else if(typeof val == 'string')
        if ((<string>val).toLocaleLowerCase() === 'true')
          return true;
        else if((<string>val).toLocaleLowerCase() === 'false')
          return false;
      break;
    case 'union':
      switch(value.$['val']) {
        case 'in_l': return <coqProto.Union<any,any>>{inl: value.$children};
        case 'in_r': return <coqProto.Union<any,any>>{inr: value.$children};
      }
      break;
    case 'option':
      return value.$['val'] === "some" ? value.$children[0] : undefined;
    case 'option_value': {
      if(value.$['val'] === 'intvalue')
        return value['option']
      else if(value.$['val'] === 'stringoptvalue')
        return value['option']
      else if(value.$['val'] === 'boolvalue')
        return value['bool'].$['val']
      else if(value.$['val'] === 'stringvalue')
        return value.$children[0]
      else
        break 
    }
    case 'option_state': {
      return {
        sync: value.$children[0],
        depr: value.$children[1],
        name: value.$children[2],
        value: value.$children[3],
      }
    }
    case 'goal':
      return <coqProto.Goal>{
        id: +value.$children[0],
        hypotheses: value.$children[1],
        goal: value.$children[2] || []
      }
    case 'goals': {
      let result = <coqProto.Goals>{goals: value.$children[0]};
      const bg_goals = <{fst: coqProto.Goal[], snd: coqProto.Goal[]}[]>value.$children[1];
      if(value.$children.length > 1) {
        result.backgroundGoals = bg_goals.reduce
          ( (bg, v) => <coqProto.UnfocusedGoalStack>{before: v.fst, next: bg, after: v.snd}
          , <coqProto.UnfocusedGoalStack>null);
        result.shelvedGoals = value.$children[2] || [];
        result.abandonedGoals = value.$children[3] || [];
      }
      return result;
    } case 'loc':
      return {start: +value.$['start'], stop: +value.$['stop']} as coqProto.Location
    case 'message_level':
      return coqProto.MessageLevel[<string>value.$['val']] as coqProto.MessageLevel;
    case 'message':
      return {
        level: value['message_level'] as coqProto.MessageLevel, 
        message: value.$children[1],
      } as coqProto.Message;
    case 'value':
      switch(value.$['val']) {
        case 'good':
          if(value['state_id'] != undefined)
            return <coqProto.Value>{
              stateId: value['state_id']
            };
          else if(value.hasOwnProperty('option'))
            return {value: value['option']} as coqProto.Value
          else if(value.$children.length===1 && value.$children[0].fst && value.$children[0].snd.fst.inl)
            return <coqProto.Value>{
              stateId: value.$children[0].fst,
              value: value.$children[0].snd.snd
            }
          else if(value.$children.length===1 && value.$children[0].fst && value.$children[0].snd.fst.inr)
            return <coqProto.Value>{
              stateId: value.$children[0].fst,
              value: value.$children[0].snd.snd,
              unfocusedStateId: value.$children[0].snd.fst.inr[0]
            }
          else if(value.$children.length===1 && value.$children[0].fst)
            return <coqProto.Value>{
              stateId: value.$children[0].fst,
              value: value.$children[0].snd
            }
          else if(value['union'])
            return <coqProto.Value>{
              value: value['union']
            }
          else
            return <coqProto.Value>{
              value: {}
            }
        case 'fail': {
          return <coqProto.Value>{
            stateId: value['state_id'],
            error: {
              range: value.$['loc_s']!=undefined && value.$['loc_e']!=undefined
                ? {start: +value.$['loc_s'], stop: +value.$['loc_e']} : null,
              message: value.$children[1] || value.$text
            }
           };
        }
      }
      break;
    // <value val="good"><state_id val="1"/></value>
    case 'feedback_content':
      switch (value.$['val'])
      { case 'workerstatus': {
        let statusStr = <string>value.$children[0].snd;
        let reSearch = /^(?:proof:[ ]*)(.*)/.exec(statusStr);
        if(reSearch)
          return <coqProto.WorkerStatus>{
            id: value.$children[0].fst,
            state: coqProto.WorkerState.Proof,
            ident: reSearch[1]
          };
        else
          return <coqProto.WorkerStatus>{
            id: value.$children[0].fst,
            state: coqProto.WorkerState[statusStr]
          };
      } case 'filedependency': {
        let file = value.$children[0] || "";
        let dependency = value.$children[1];
        return <coqProto.FileDependency>{
          filename: file,
          dependsOn: dependency
        };
      } case 'fileloaded':
        return <coqProto.FileLoaded>{
          module: value.$children[0],
          filename: value.$children[1]
        };
      case 'errormsg':
        return <coqProto.ErrorMessage>{
          location: value.$children[0],
          message: value.$children[1]
        };
      case 'processingin':
      case 'processed':
      case 'incomplete':
      case 'complete':
        return <coqProto.SentenceFeedback>{
          status: coqProto.SentenceStatus[<string>value.$['val']],
          worker: value.$children[0]
        }
      case 'custom': {
        return {
          type: value.$children[1] as string,
          location: value.$children[0] as coqProto.Location,
          data: value.$children[2],
        } as coqProto.CustomFeedback;
      } default:
        return value;
      }
    case 'feedback':
      if(value.$['object'] === 'state') {
        let result = <coqProto.StateFeedback>{
          stateId: +value['state_id'],
          route: +value.$['route'],
          };
        const workerStatus = <coqProto.WorkerStatus[]>value.$children
            .filter((value,i,a) => value.hasOwnProperty('id') && value.hasOwnProperty('state'));
        const fileDependencies = <Map<string,string[]>>value.$children
            .filter((value,i,a) => value.hasOwnProperty('filename') && value.hasOwnProperty('dependsOn'))
            .reduce((m:any,curr:coqProto.FileDependency,currIdx:number,a: any[]) => {
              if(!m.has(curr.filename))
                m.set(curr.filename, []);
              m.get(curr.filename).push(curr.dependsOn) 
            }, new Map<string,string[]>());
        const fileLoaded = <coqProto.FileLoaded>value.$children
            .find((value,i,a) => value.hasOwnProperty('module') && value.hasOwnProperty('filename'));
        const sentenceFeedback = <coqProto.SentenceFeedback>value.$children
            .find((value,i,a) => value.hasOwnProperty('status') && value.hasOwnProperty('worker'));
        const error = <coqProto.ErrorMessage>value.$children
            .find((value,i,a) => value.hasOwnProperty('location') && value.hasOwnProperty('message'));
        const custom = <coqProto.CustomFeedback>value.$children
            .find((value,i,a) => value.hasOwnProperty('location') && value.hasOwnProperty('data') && value.hasOwnProperty('type'));
        if (workerStatus && workerStatus.length > 0)
          result.workerStatus = workerStatus;
        if (fileDependencies && fileDependencies.size > 0)
          result.fileDependencies = fileDependencies;
        if (fileLoaded)
          result.fileLoaded = fileLoaded;
        if (sentenceFeedback)
          result.sentenceFeedback = sentenceFeedback;
        if (error)
          result.error = error;
        if(custom)
            result.custom = custom;          
        return result;
      } else if(value.$['object'] === 'edit') {
        return <coqProto.EditFeedback>{
          editId: +value['edit_id'],
          route: +value.$['route'],
          error: <coqProto.ErrorMessage>value.$children
            .find((value,i,a) => value.hasOwnProperty('message') && value.hasOwnProperty('location'))            
        }        
      }
      break;
  }
  return value;
}
