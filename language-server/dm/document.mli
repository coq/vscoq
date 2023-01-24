(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Types
open Lsp.LspData

(** This file defines operations on the content of a document (text, parsing
    of sentences, scheduling). *)

(** The document gathers the text, which is partially validated (parsed into
    sentences *)
type document

val create_document : string -> document
(** [create_document text] creates a fresh document with content defined by
    [text]. *)

val id_of_doc : document -> int
(** Unique id of the document *)

val validate_document : document -> sentence_id_set * document
(** [validate_document doc] parses the document without forcing any execution
    and returns the set of invalidated sentences *)

val parse_errors : document -> (sentence_id * (Loc.t option * string)) list
(** [parse_errors doc] returns the list of sentences which failed to parse
    (see validate_document) together with their error message *)

type text_edit = Range.t * string

val apply_text_edits : document -> text_edit list -> document
(** [apply_text_edits doc edits] updates the text of [doc] with [edits]. The
    new text is not parsed or executed. *)

type parsed_ast =
  | ValidAst of ast * Vernacextend.vernac_classification * Tok.t list (* the list of tokens generating ast, a sort of fingerprint to compare ASTs  *)
  | ParseError of string Loc.located

type sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Synterp.t; (* st used to parse this sentence *)
  scheduler_state_before : Scheduler.state;
  scheduler_state_after : Scheduler.state;
  ast : parsed_ast;
  id : sentence_id;
}

val sentences : document -> sentence list

val get_sentence : document -> sentence_id -> sentence option
val sentences_before : document -> int -> sentence list

val find_sentence : document -> int -> sentence option
(** [find_sentence doc loc] finds the sentence containing the loc *)

val find_sentence_before : document -> int -> sentence option
(** [find_sentence_before doc loc] finds the last sentence before the loc *)

val parsed_loc : document -> int
(** the last loc of the document which was parsed *)

val end_loc : document -> int
(** the last loc of the document *)

val schedule : document -> Scheduler.schedule

val text : document -> string
(** the whole text *)

(* Fishy APIs *)
val range_of_exec_id : document -> Stateid.t -> Range.t
val range_of_coq_loc : document -> Loc.t -> Range.t

val position_of_loc : document -> int -> Position.t
val position_to_loc : document -> Position.t -> int

