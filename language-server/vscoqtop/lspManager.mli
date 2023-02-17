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

type event
type events = event Sel.event list

val lsp : event Sel.event

val handle_event : event -> events
val pr_event : event -> Pp.t

val init : Coqargs.injection_command list -> unit

val coqtopSearchResult : id:string -> string -> string -> unit