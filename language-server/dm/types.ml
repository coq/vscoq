(**************************************************************************)
(*                                                                        *)
(*                                 VSCoq                                  *)
(*                                                                        *)
(*                   Copyright INRIA and contributors                     *)
(*       (see version control and README file for authors & dates)        *)
(*                                                                        *)
(**************************************************************************)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License.         *)
(*   See LICENSE file.                                                    *)
(*                                                                        *)
(**************************************************************************)
open Protocol.LspWrapper

type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t

module RangeList = struct

  type t = Range.t list
  
  let insert_or_merge_range r ranges =
    let ranges = List.sort Range.compare (r :: ranges) in
    let rec insert_or_merge_sorted_ranges r1 = function
      | [] -> [r1]
      | r2 :: l ->
        if Range.included ~in_:r1 r2 then (*since the ranges are sorted, only r2 can be included in r1*)
          insert_or_merge_sorted_ranges r1 l
        else if Range.prefixes ~in_:r2 r1 then
          begin
            let range = Range.{start = r1.Range.start; end_ = r2.Range.end_} in
            insert_or_merge_sorted_ranges range l
          end
        else
          r1 :: (insert_or_merge_sorted_ranges r2 l)
    in
    insert_or_merge_sorted_ranges (List.hd ranges) (List.tl ranges)

  let rec remove_or_truncate_range r = function
  | [] -> []
  | r1 :: l ->
    if Range.equals r r1
    then
      l
    else if Range.strictly_included ~in_: r1 r then
      Range.{ start = r1.Range.start; end_ = r.Range.start} :: Range.{ start = r.Range.end_; end_ = r1.Range.end_} :: l
    else if Range.prefixes ~in_:r1 r then
      Range.{ start = r.Range.end_; end_ = r1.Range.end_} :: l
    else if Range.postfixes ~in_:r1 r then
      Range.{ start = r1.Range.start; end_ = r.Range.start} :: l
    else
      r1 :: (remove_or_truncate_range r l)

    let rec cut_from_range r = function
    | [] -> []
    | r1 :: l ->
      let (<=) x y = Position.compare x y <= 0 in
      if r.Range.start <= r1.Range.start then
        l
      else if r.Range.start <= r1.Range.end_ then
        Range.{start = r1.Range.start; end_ = r.Range.start} :: l
      else
        r1 :: (cut_from_range r l)

end


type exec_overview = {
  prepared: RangeList.t;
  processing : RangeList.t;
  processed : RangeList.t;
}

let empty_overview = {processing = []; processed = []; prepared = []}

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  module Quickfix = struct
    type t = unit
    let from_exception _ = Ok([])
    let pp = Pp.mt
    let loc _ = Loc.make_loc (0,0)
  end
[%%endif]

type text_edit = Range.t * string

type link = {
  write_to :  Unix.file_descr;
  read_from:  Unix.file_descr;
}

type error = {
  code: Jsonrpc.Response.Error.Code.t option;
  message: string;
}

type 'a log = Log : 'a -> 'a log
