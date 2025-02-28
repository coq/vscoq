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

type 'a log = Log : 'a -> 'a log

val mk_log : string -> (?force:bool -> (unit -> string) -> unit) log
val logs : unit -> string list

type event = string
type events = event Sel.Event.t list

val lsp_initialization_done : unit -> events
val handle_event : event -> unit

val worker_initialization_begins : unit -> unit
val worker_initialization_done : fwd_event:(event -> unit) -> unit

(* debug messages coming from either the language server of Coq *)
val debug : event Sel.Event.t

[%% if coq = "8.18" || coq = "8.19" || coq = "8.20" ]
val feedback_add_feeder_on_Message : (Feedback.route_id -> Stateid.t -> Feedback.doc_id -> Feedback.level -> Loc.t option -> 'a list -> Pp.t -> unit) -> int
[%%else]
val feedback_add_feeder_on_Message : (Feedback.route_id -> Stateid.t  -> Feedback.doc_id -> Feedback.level -> Loc.t option -> Quickfix.t list -> Pp.t -> unit) -> int
[%%endif]
val feedback_delete_feeder : int -> unit