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

(** Simple event library - No asymc monads, No threads, No exceptions *)

type 'a event
type 'a res = ('a,exn) result
type cancellation_handle
val cancel : cancellation_handle -> unit

(** System events one can wait for *)
val on_line : Unix.file_descr -> (string res -> 'a) -> 'a event * cancellation_handle
val on_bytes : Unix.file_descr -> int -> (Bytes.t res -> 'a) -> 'a event * cancellation_handle
val on_death_of : pid:int -> (Unix.process_status -> 'a) -> 'a event * cancellation_handle

val on_ocaml_value : Unix.file_descr -> ('b res -> 'a) -> 'a event * cancellation_handle
val on_httpcle : Unix.file_descr -> (Bytes.t res -> 'a) -> 'a event * cancellation_handle

(** Synchronization events between components (worker pool and a task queue) *)
val on_queues : 'b Queue.t -> 'c Queue.t -> ('b -> 'c -> 'a) -> 'a event * cancellation_handle

(** A way to feed the event queue *)
val on_queue : 'b Queue.t -> ('b -> 'a) -> 'a event * cancellation_handle

(** Mix regular computations with blocking event (reified) *)
val now : 'a -> 'a event

val map : ('a -> 'b) -> 'a event -> 'b event

(** for debug printing *)
val name : string -> 'a event -> 'a event
(** a recurrent event is never removed from the todo set, that is, when
   ready a copy of it is added back automatically *)
val make_recurring : 'a event -> 'a event
(** convenience adaptor to drop the cancellation handle *)
val uncancellable : 'a event * cancellation_handle -> 'a event
(** it is unusual to make a regular computation cancellable, hence the
   event constructor does not recurn the cancellation handle. Here the way
   to recover it *)
val cancellation_handle : 'e event -> cancellation_handle
(** lower integers correspond to hight priorities (as in Unix nice) *)
val set_priority : int -> 'a event -> 'a event

(** The main loop goes like this

    type top_event =
    | NotForMe of Component.event
    | Echo of string

    let echo : top_event event =
      on_line Unix.stdin (function
        | Ok s -> Echo s
        | Error _ -> Echo "error")
      |> uncancellable
      |> make_recurrent

    let handle_event = function
    | NotForMe e ->
        List.map (map (fun x -> NotForMe x)) (Component.handle_event e)
    | Echo text ->
        Printf.eprintf "echo: %s\n" text;
        []

    let rec loop evs =
      let ready, evs = pop evs in
      let new_evs = handle_event ready in
      loop (enqueue evs new_evs)

    let main () =
      loop (enqueue empty [echo; ...])

 *)

type 'a todo
val pp_todo : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a todo -> unit

val empty : 'a todo
val size : 'a todo -> int
val enqueue : 'a todo -> 'a event list -> 'a todo
val nothing_left_to_do : 'a todo -> bool
val only_recurring_events : 'a todo -> bool

(** raises Failure if there is nothing left to do *)
val pop : 'a todo -> 'a * 'a todo
val pop_opt : 'a todo -> 'a option * 'a todo

val pop_timeout : stop_after_being_idle_for:float -> 'a todo -> 'a option * 'a todo

val wait : 'a todo -> 'a list * 'a list * 'a list * 'a todo
val wait_timeout : stop_after_being_idle_for:float -> 'a todo -> 'a list * 'a list * 'a list * 'a todo


