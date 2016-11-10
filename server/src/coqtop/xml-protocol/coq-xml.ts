'use strict';
import * as events from 'events';
import * as sax from 'sax';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import * as util from 'util';
import {Deserialize} from './deserialize.base';

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

export function escapeXml(unsafe: string) : string {
    return unsafe.replace(/[<>&'"]/g, function (c) {
        switch (c) {
            case '<': return '&lt;';
            case '>': return '&gt;';
            case '&': return '&amp;';
            case '\'': return '&apos;';
            case '"': return '&quot;';
            default: return c;
        }
    });
}

export class XmlStream extends events.EventEmitter {
  private stack : Node[] = [];
  
  public constructor(private inputStream: NodeJS.ReadableStream, private readonly deserializer: Deserialize, callbacks?: EventCallbacks) {
    super();
    
    if(callbacks) {
      if(callbacks.onValue)
        this.on('response: value', (x:coqProto.Value) => callbacks.onValue(x));
      if(callbacks.onStateFeedback)
        this.on('response: state-feedback', (x:coqProto.StateFeedback) => callbacks.onStateFeedback(x));
      if(callbacks.onEditFeedback)
        this.on('response: edit-feedback', (x:coqProto.EditFeedback) => callbacks.onEditFeedback(x));
      if(callbacks.onMessage)
        this.on('response: message', (x:coqProto.Message) => callbacks.onMessage(x));
      if(callbacks.onOther)
        this.on('response', (x:any) => callbacks.onOther(x));
      if(callbacks.onError)
        this.on('error', (x:any) => callbacks.onError(x));
    }
    
    let options : sax.SAXOptions | {strictEntities: boolean} = {
      lowercase: true,
      trim: false,
      normalize: false,
      xmlns:false,
      position: false,
      strictEntities: false,
      noscript: true
    };
    
    let saxStream = sax.createStream(false,options);
    saxStream.on('error', (err:any) => this.onError(err));
    saxStream.on('opentag', (node:sax.Tag) => this.onOpenTag(node));
    saxStream.on('closetag', (tagName:string) => this.onCloseTag(tagName));
    saxStream.on('text', (text:string) => this.onText(text));
    saxStream.on('end', () => this.onEnd());
    saxStream.write('<coqtoproot>'); // write a dummy root node to satisfy the xml parser
    this.inputStream.pipe(saxStream);
  }
  
  private onError(err:any[]) {
    this.emit('error', err);
  }

  private annotateTextMode = false;
  private textStack : text.ScopedText[] = [];

  private onOpenTag(node: sax.Tag) {
    if(node.name === 'coqtoproot')
      return;

    if(this.annotateTextMode) {
      let txt : text.ScopedText = {scope: node.name, attributes: node.attributes, text: []};
      this.textStack.push(txt);
    } else if (node.name === 'richpp') {
      let txt : text.ScopedText = {scope: "", attributes: node.attributes, text: []};
      this.annotateTextMode = true;
      this.textStack = [txt];
    } else {
      let topNode = {
        $name: node.name,
        $: node.attributes,
        $text: "",
        $children: <any[]>[]
      };
      this.stack.push(topNode);
    }
  }

  private onCloseTag(closingTagName : string) {
    if(closingTagName === 'coqtoproot') {
      this.emit('error', 'malformed XML input stream has too many closing tags');
      return;
    }

    if(this.annotateTextMode) {
      const current = this.textStack.pop();
      if(this.textStack.length > 0) {
        const top = this.textStack[this.textStack.length-1];
        if(top.text instanceof Array)
          top.text.push(current);
        else
          top.text = [top.text, current]
        return;
      } else {
        let newTop = this.stack[this.stack.length - 1];
        newTop.$children.push(current);
        newTop['richpp'] = current;
        this.annotateTextMode = false;
        return; 
      }
    } else if (this.stack.length === 0)
      return;
    else {
      let currentTop = this.stack.pop();
      let tagName = currentTop.$name;
      let value = this.deserializer.deserialize(currentTop);
      
      if (this.stack.length > 0) {
        let newTop = this.stack[this.stack.length - 1];
        newTop.$children.push(value);
        newTop[tagName] = value;
        if(closingTagName === 'richpp') {
          this.annotateTextMode = false;
        }
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
  }
  
  private onText(text : string) {
    if(this.annotateTextMode) {
      const top = this.textStack[this.textStack.length-1];
      if(top.text instanceof Array)
        top.text.push(text);
      else
        top.text = [top.text, text];
    } else if(this.stack.length > 0) {
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
