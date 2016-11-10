'use strict';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import {Deserialize, Node} from './deserialize.base';

export class Deserialize_8_5 extends Deserialize {
  public deserialize(value: Node) : coqProto.CoqValue {    
    return super.deserialize(value);
  }

  public static readonly baseVersion = "8.5";
}
