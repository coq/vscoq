'use strict';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import * as util from 'util';
import {Deserialize_8_5} from './deserialize.8.5';
import {Deserialize_8_6} from './deserialize.8.6';

const DEFAULT_DESERIALIZER = Deserialize_8_6;

export function createDeserializer(version: string) {
  if(version.startsWith('8.5'))
    return new Deserialize_8_5();
  else if(version.startsWith('8.6'))    
    return new Deserialize_8_6();
  else {
    console.warn(`Unknown version of Coq: ${version}; falling back to ${DEFAULT_DESERIALIZER.baseVersion}`);
    return new DEFAULT_DESERIALIZER();
  }
}
