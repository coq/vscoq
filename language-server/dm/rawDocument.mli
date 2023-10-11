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

type t

val create : DidOpenTextDocumentParams.t -> t
val text : t -> string

val compare_lines : t -> (string -> unit) -> unit

val position_of_loc : t -> int -> Position.t
val loc_of_position : t -> Position.t -> int
val end_loc : t -> int

val apply_text_edits : t -> TextEdit.t list -> t
val range_of_loc : t -> Loc.t -> Range.t
val word_at_position: t -> Position.t -> string option

(** Tests if document text contains only whitespace between the two provided
    locations, included *)
val only_whitespace_between : t -> int -> int -> bool