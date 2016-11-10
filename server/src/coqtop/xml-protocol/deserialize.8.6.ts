'use strict';
import * as coqProto from '../coq-proto';
import * as text from '../../util/AnnotatedText';
import {Deserialize, Node} from './deserialize.base';

export class Deserialize_8_6 extends Deserialize {
  public deserialize(value: Node) : coqProto.CoqValue {
    const [tag, attrs, children] = [value.$name, value.$, value.$children]
    try {
    switch(tag) {
      case 'message':
        return {
          level: children[0] as coqProto.MessageLevel,
          location: children[1],
          message: children[2],
        } as coqProto.Message;
      case 'ltacprof':
        return {
          total_time: +attrs['total_time'],
          tactics: children
        } as coqProto.LtacProfResults;
      case 'ltacprof_tactic':
        return {
          name: attrs['name'],
          statistics: {
            total: +attrs['total'],
            local: +attrs['local'],
            num_calls: +attrs['ncalls'],
            max_total: +attrs['max_total']},
            tactics: children
          } as coqProto.LtacProfTactic;
      default:
        return super.deserialize(value);
    }}
    catch(err) {
      debugger;
    }
  }

  public static readonly baseVersion = "8.6";
}
