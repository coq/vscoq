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

(** The event manager is in charge of the actual event of tasks (as
    defined by the scheduler), caching event states and invalidating
    them. It can delegate to worker processes via DelegationManager *)

(** Execution state, includes the cache *)
type state
val init : Vernacstate.t -> state
val invalidate : Scheduler.schedule -> sentence_id -> state -> state
val errors : state -> (sentence_id * (Loc.t option * string)) list
val feedback : state -> (sentence_id * (Feedback.level * Loc.t option * string)) list
val shift_locs : state -> int -> int -> state
val executed_ids : state -> sentence_id list
val is_executed : state -> sentence_id -> bool
val is_remotely_executed : state -> sentence_id -> bool
val get_parsing_state_after : state -> sentence_id -> Vernacstate.Parser.t option
val get_proofview : state -> sentence_id -> Proof.data option

(** Events for the main loop *)
type event type events = event Sel.event list
val pr_event : event -> Pp.t
val local_feedback : event Sel.event
val handle_event : event -> state -> (state option * events)

(** Execution happens in two steps. In particular the event one takes only
    one task at a time to ease checking for interruption *)
type prepared_task
val build_tasks_for : Document.document -> state -> sentence_id -> Vernacstate.t * prepared_task list
val execute : doc_id:Feedback.doc_id -> state -> Vernacstate.t * events * bool -> prepared_task -> (state * Vernacstate.t * events * bool)

(** Coq toplevels for delegation without fork *)
module ProofWorkerProcess : sig
  type options
  val parse_options : string list -> options * string list
  val main : st:Vernacstate.t -> options -> unit
  val log : string -> unit
end
