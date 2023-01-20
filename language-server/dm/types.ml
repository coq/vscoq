(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t
type ast = Synterp.vernac_entry_control

module Position : sig
  type t = { line : int; char : int }
  val compare : t -> t -> int
  val to_string : t -> string
end = struct
  type t = { line : int; char : int; }

  let compare pos1 pos2 =
    match Int.compare pos1.line pos2.line with
    | 0 -> Int.compare pos1.char pos2.char
    | x -> x

  let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.char

end

module Range = struct
  type t = { start : Position.t; stop : Position.t; }
end 

type text_edit = Range.t * string

let initial_synterp_state = Summary.empty_frozen

let parsing_state_of_synterp_state = Summary.project_from_summary