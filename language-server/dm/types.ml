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
open Lsp.Types

type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t

type exec_overview = {
  prepared: Range.t list;
  processing : Range.t list;
  processed : Range.t list;
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

type 'a log = Log : 'a -> 'a log
