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

open Types
open CompletionItems
open Lsp.LspData

(** The event manager is in charge of the actual event of tasks (as
    defined by the scheduler), caching event states and invalidating
    them. It can delegate to worker processes via DelegationManager *)

type delegation_mode =
  | CheckProofsInMaster
  | SkipProofs
  | DelegateProofsToWorkers of { number_of_workers : int }

type options = {
  delegation_mode : delegation_mode;
}

(** Execution state, includes the cache *)
type state
val init : Vernacstate.t -> state
val set_options : options -> unit
val invalidate : Scheduler.schedule -> sentence_id -> state -> state
val errors : state -> (sentence_id * (Loc.t option * string)) list
val feedback : state -> (sentence_id * (Feedback.level * Loc.t option * string)) list
val shift_locs : state -> int -> int -> state
val executed_ids : state -> sentence_id list
val is_executed : state -> sentence_id -> bool
val is_remotely_executed : state -> sentence_id -> bool
val get_proof : state -> sentence_id -> Proof.t option
val get_proofview : state -> sentence_id -> Proof.data option
val get_context : state -> sentence_id -> (Evd.evar_map * Environ.env) option
val get_lemmas : Evd.evar_map -> Environ.env -> completion_item list

(** Events for the main loop *)
type event type events = event Sel.event list
val pr_event : event -> Pp.t
val local_feedback : event Sel.event
val handle_event : event -> state -> (state option * events)

(** Execution happens in two steps. In particular the event one takes only
    one task at a time to ease checking for interruption *)
type prepared_task
val build_tasks_for : Scheduler.schedule -> state -> sentence_id -> Vernacstate.t * prepared_task list
val execute : doc_id:Feedback.doc_id -> state -> Vernacstate.t * events * bool -> prepared_task -> (state * Vernacstate.t * events * bool)

(** Coq toplevels for delegation without fork *)
module ProofWorkerProcess : sig
  type options
  val parse_options : string list -> options * string list
  val main : st:Vernacstate.t -> options -> unit
  val log : string -> unit
end
