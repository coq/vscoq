(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Simple event library - No asymc monads, No threads, No exceptions *)

type 'a event
type 'a res = ('a,exn) result

(** System events one can wait for *)
val on_line : Unix.file_descr -> (string res -> 'a) -> 'a event
val on_bytes : Unix.file_descr -> int -> (Bytes.t res -> 'a) -> 'a event
val on_death_of : pid:int -> (Unix.process_status -> 'a) -> 'a event

val on_ocaml_value : Unix.file_descr -> ('b res -> 'a) -> 'a event
val on_httpcle : Unix.file_descr -> (Bytes.t res -> 'a) -> 'a event

(** Synchronization events between components (worker pool and a task queue) *)
val on_queues : 'b Queue.t -> 'c Queue.t -> ('b -> 'c -> 'a) -> 'a event

(** A way to feed the event queue *)
val on_queue : 'b Queue.t -> ('b -> 'a) -> 'a event

(** Dummy event *)
val now : 'a -> 'a event

val map : ('a -> 'b) -> 'a event -> 'b event

(** The main loop goes like this

    type top_event =
    | NotForMe of Component.event
    | Echo of string

    let echo : top_event event =
      on_line Unix.stdin (function
      | Ok s -> Echo s
      | Error _ -> Echo "error")

    let handle_event = function
    | NotForMe e -> List.map (map (fun x -> NotForMe x)) (Component.handle_event e)
    | Echo text ->
        Printf.eprintf "echo: %s\n" text;
        [echo]

    let rec loop evs =
      let ready, waiting = wait evs in
      let new_evs_l = List.map handle_event ready in
      loop (waiting @ List.concat new_evs_l)

    let main () =
      loop [echo; ...]

 *)

val wait : ?stop_after_being_idle_for:float -> 'a event list -> 'a list * 'a event list
