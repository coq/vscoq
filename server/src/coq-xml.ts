'use strict';
import * as events from 'events';
import * as sax from 'sax';
import * as coqProto from './coq-proto';
// var entities = require('entities'); 

export interface EventCallbacks {
  onValue?: (x: coqProto.Value) => void;
  onStateFeedback? : (feedback: coqProto.StateFeedback) => void;
  onEditFeedback? : (feedback: coqProto.EditFeedback) => void;
  onMessage? : (msg: coqProto.Message) => void;
  onOther? : (x: any) => void;
  onError? : (x: any) => void;
}

export interface Node {
  $name: string;
  $text: string;
  /* attributes */
  $: { [key:string]:coqProto.CoqValue };
  /* children */
  $children : coqProto.CoqValue[];
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
    case 'goal':
      return <coqProto.Goal>{
        id: +value.$children[0],
        hypotheses: value.$children[1],
        goal: value.$children[2]
      }
    case 'goals': {
      let result = <coqProto.Goals>{goals: value.$children[0]};
      if(value.$children.length > 1) {
        result.backgroundGoals = value.$children[1];
        result.shelvedGoals = value.$children[2];
        result.abandonedGoals = value.$children[3];
      }
      return result;
    } case 'loc':
      return <coqProto.Location>{
        start: +value.$['start'],
        stop: +value.$['stop']
      }
    case 'message_level':
      return <coqProto.MessageLevel>coqProto.MessageLevel[<string>value.$['val']];
    case 'message':
      return <coqProto.Message>{
        level: <coqProto.MessageLevel>value['message_level'],
        message: value['string']
      }
    case 'value':
      switch(value.$['val']) {
        case 'good':
          if(value['state_id'] != undefined)
            return <coqProto.Value>{
              stateId: value['state_id']
            };
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
          else if(value['option'] && value['option'].$['val'] === 'some' && value['option']['goals'])
            return <coqProto.Value>{
              value: value['option']['goals']
            }
          else if(value['option'] && value['option'].$['val'] === 'none')
            return <coqProto.Value>{
              value: {}
            }
          break;
        case 'fail': {
          return <coqProto.Value>{
            stateId: value['state_id'],
            error: {
              location: value.$['loc_s']!=undefined && value.$['loc_e']!=undefined
                ? {start: +value.$['loc_s'], stop: +value.$['loc_e']} : null,
              message: value.$text
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
        let file = value.$children[0].some || "";
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
      }
      break;
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
            .reduce((m,curr:coqProto.FileDependency,currIdx,a) => {
              if(!m.has(curr.filename))
                m.set(curr.filename, []);
              m.get(curr.filename).push(curr.dependsOn) 
            }, new Map<string,string[]>());
        const fileLoaded = <coqProto.FileLoaded>value.$children
            .find((value,i,a) => value.hasOwnProperty('module') && value.hasOwnProperty('filename'));
        const sentenceFeedback = <coqProto.SentenceFeedback>value.$children
            .find((value,i,a) => value.hasOwnProperty('status') && value.hasOwnProperty('worker'));
        const error= <coqProto.ErrorMessage>value.$children
            .find((value,i,a) => value.hasOwnProperty('location') && value.hasOwnProperty('message'));
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

export class XmlStream extends events.EventEmitter {
  
  private inputStream : NodeJS.ReadableStream;
  private stack : Node[] = [];
  
  public constructor(stream: NodeJS.ReadableStream, callbacks?: EventCallbacks) {
    super();
    this.inputStream = stream;
    
    if(callbacks) {
      if(callbacks.onValue)
        this.on('response: value', (x) => callbacks.onValue(x));
      if(callbacks.onStateFeedback)
        this.on('response: state-feedback', (x) => callbacks.onStateFeedback(x));
      if(callbacks.onEditFeedback)
        this.on('response: edit-feedback', (x) => callbacks.onEditFeedback(x));
      if(callbacks.onMessage)
        this.on('response: message', (x) => callbacks.onMessage(x));
      if(callbacks.onOther)
        this.on('response', (x) => callbacks.onOther(x));
      if(callbacks.onError)
        this.on('error', (x) => callbacks.onError(x));
    }
    
    let options : sax.SAXOptions = {
      lowercase: true,
      trim: true,
      normalize: false,
      xmlns:false,
      position: false,
      strictEntities: false,
      noscript: true
    };
    
    let saxStream = sax.createStream(false,options);
    saxStream.on('error', (err) => this.onError(err));
    saxStream.on('opentag', (node) => this.onOpenTag(node));
    saxStream.on('closetag', (tagName) => this.onCloseTag(tagName));
    saxStream.on('text', (text) => this.onText(text));
    saxStream.on('end', () => this.onEnd());
    saxStream.write('<coqtoproot>'); // write a dummy root node to satisfy the xml parser
    stream.pipe(saxStream);
  }
  
  private onError(err) {
    this.emit('error', err);
  }

  private onOpenTag(node: sax.Tag) {
    if(node.name === 'coqtoproot')
      return;
      
    let topNode = {
      $name: node.name,
      $: node.attributes,
      $text: "",
      $children: []
    };
    this.stack.push(topNode);
  }


  private onCloseTag(closingTagName : string) {
    if(closingTagName === 'coqtoproot') {
      this.emit('error', 'malformed XML input stream has too many closing tags');
      return;
    }
    if (this.stack.length === 0)
      return;

    let currentTop = this.stack.pop();
    let tagName = currentTop.$name;
    let value : coqProto.CoqValue = toCoqValue(currentTop);
    
    if (this.stack.length > 0) {
      let newTop = this.stack[this.stack.length - 1];
      newTop.$children.push(value);
      newTop[tagName] = value;
    } else if(currentTop.$name === 'feedback') {
      this.emit('response', value);
      if(currentTop.$['object'] === 'edit')
        this.emit('response: edit-feedback', value);
      else if(currentTop.$['object'] === 'state')
        this.emit('response: state-feedback', value);
    } else {
      this.emit('response', value);
      this.emit('response: ' + currentTop.$name, value);
    }
  }
  
    // <value val="good"><state_id val="1"/></value>
  
    // <value val="good">
    //   <pair>
    //     <state_id val="2"/>
    //     <pair>
    //       <union val="in_l">  <unit/> </union>
    //       <string></string>
    //     </pair>
    //   </pair>
    // </value>
  
    // <feedback object="state" route="0">
    //   <state_id val="1"/>
    //   <feedback_content val="workerstatus">
    //     <pair>
    //       <string>proofworker:0</string>
    //       <string>Idle</string>
    //     </pair>
    //   </feedback_content>
    // </feedback>

  
  private onText(text : string) {
    if(this.stack.length > 0) {
      // let plainText = entities.decodeXML(text);
      this.stack[this.stack.length-1].$text += text;
    }
  }
  
  private onEnd() {
    this.emit('end');
  }
  
  public pause() {
    this.inputStream.pause();
  }
  
  public resume() {
    this.inputStream.resume();
  }
  
}

  
// 
// /**
//  * @param ReadSteam inStream the stream to be parsed
//  */
// flow = module.exports = function(inStream, options) {
//     var emitter = new EventEmitter()
//       , saxOptions = {}
//       , saxStream = null
//       , stack = []
//       , topNode = null
//     ;
// 
//     options = options || {};
//     options.preserveMarkup = options.preserveMarkup  || flow.SOMETIMES;
//     options.simplifyNodes = options.hasOwnProperty('simplifyNodes') ? options.simplifyNodes : true;
// 
//     saxOptions.lowercase = options.hasOwnProperty('lowercase') ? options.lowercase : true;
//     saxOptions.trim = options.hasOwnProperty('trim') ? options.trim : true;
//     saxOptions.normalize = options.hasOwnProperty('normalize') ? options.normalize : true;
// 
//     saxStream = sax.createStream(options.strict || false, saxOptions);
// 
//     saxStream.on('opentag', function(node) {
//         //Ignore nodes we don't care about.
//         if(stack.length === 0 && !emitter.listeners('tag:' + node.name).length) {
//             return;
//         }
// 
//         topNode = {
//             $name: node.name,
//             $attrs: node.attributes,
//             $markup: []
//         };
//         stack.push(topNode);
//     });
// 
//     saxStream.on('text', function(text) {
//         if(topNode) {
//             topNode.$markup.push(text);
//         }
//     });
// 
//     saxStream.on('script', function(script) {
//         topNode.$script = script;
//     });
// 
//     saxStream.on('closetag', function(tagName) {
//         var compressed
//           , newTop = null
//         ;
// 
//         //If we're not going to send out a node, goodbye!
//         if(stack.length === 0) { return; }
// 
//         //Objectify Markup if needed...
//         if(options.preserveMarkup <= flow.NEVER) {
//             topNode.$markup = helper.condenseArray(topNode.$markup);
//             topNode = helper.objectifyMarkup(topNode);
//         } else if(options.preserveMarkup === flow.SOMETIMES) {
//             compressed = helper.condenseArray(topNode.$markup);
//             if(helper.shouldObjectifyMarkup(compressed)) {
//                 topNode.$markup = compressed;
//                 topNode = helper.objectifyMarkup(topNode);
//             }
//         }
// 
//         //emit the node
//         emitter.emit(
//             'tag:' + tagName,
//             options.simplifyNodes ? helper.simplifyNode(topNode) : topNode
//         );
// 
//         //Pop stack, and add to parent node
//         stack.pop();
//         if(stack.length > 0) {
//             newTop = stack[stack.length-1];
//             newTop.$markup.push(topNode);
//         }
//         topNode = newTop;
//     });
// 
//     saxStream.on('end', function(){
//         emitter.emit('end');
//     });
// 
//     inStream.pipe(saxStream);
// 
//     emitter.pause = function(){
//         inStream.pause();
//     };
// 
//     emitter.resume = function() {
//         inStream.resume();
//     };
// 
//     return emitter;
// };
// 
// flow.ALWAYS = 1;
// flow.SOMETIMES = 0;
// flow.NEVER = -1;
// 
// flow.toXml = function(node, name) {
//     var output = ''
//       , keys
//     ;
// 
//     if(node.constructor === Array) {
//         node.forEach(function(subNode){
//             output += flow.toXml(subNode, name);
//         });
//         return output;
//     }
// 
//     if(!name && node.$name) {name = node.$name;}
// 
//     if(name) {
//         output = '<' + name;
// 
//         if(node.$attrs && typeof node.$attrs === 'object') {
//             keys = Object.keys(node.$attrs);
//             keys.forEach(function(key){
//                 output += ' ' + key + '=' + JSON.stringify('' + node.$attrs[key]);
//             });
//         }
//         output += '>';
//     }
// 
//     if(node === null || node === undefined) {
//         //do nothing. Empty on purpose
//     } else if (typeof node === 'object') {
//         keys = Object.keys(node);
//         keys.forEach(function(key){
//             var value = node[key];
//             switch(key) {
//                 case '$name':
//                 case '$attrs':
//                     //Do nothing. Already taken care of
//                 break;
// 
//                 case '$text':
//                 case '$markup':
//                     output += flow.toXml(value);
//                 break;
// 
//                 case '$script':
//                     output += flow.toXml(value, 'script');
//                 break;
// 
//                 default:
//                     output += flow.toXml(value, key);
//             }
//         });
//     } else {
//         output += node;
//     }
// 
//     if(name) { output += '</' + name + '>'; }
//     return output;
// };
//
