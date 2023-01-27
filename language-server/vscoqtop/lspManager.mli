(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type event
type events = event Sel.event list

val lsp : event Sel.event

val handle_event : event -> events
val pr_event : event -> Pp.t

val init : Coqargs.injection_command list -> unit

val coqtopSearchResult : id:string -> string -> string -> unit