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
open Base
open Sel

[@@@warning "-27"]

(************************ UTILS **********************************************)

(* we don't want to lock forever doing tests, esp if we know pop_opt would be
   stuck *)
let wait_timeout todo =
  let ready, todo = pop_timeout ~stop_after_being_idle_for:0.1 todo in
  [%test_eq: bool] (Option.is_none ready) true;
  [%test_eq: bool] (nothing_left_to_do todo) false;
  ready, todo

(* match a string list against a rex list, useful for errors *)
let osmatch r s =
  match s with
  | None -> false
  | Some s -> Str.string_match (Str.regexp r) s 0
  
let b2s = function
  | Ok b -> Bytes.to_string b
  | Error x -> Stdlib.Printexc.to_string x

let s2s = function
  | Ok s -> s
  | Error x -> Stdlib.Printexc.to_string x

let write_pipe write s =
  let len = String.length s in
  let rc = Unix.write write (Bytes.of_string s) 0 len in
  [%test_eq: int] rc len

let pipe () =
  let read, write = Unix.pipe () in
  read, write_pipe write

let read_leftover read n =
  let b = Bytes.create n in
  let rc = Unix.read read b 0 n in
  [%test_eq: int] rc n;
  Bytes.to_string b
  
(*****************************************************************************)

(* pop_opt terminates *)
let%test_unit "sel.wait.empty" =
  let ready, todo = pop_opt empty in
  [%test_eq: bool] (Option.is_none ready) true;
  [%test_eq: bool] (nothing_left_to_do todo) true;
;;

(* tasks are returned according to their priority *)
let %test_unit "sel.wait.prio" =
  let todo = enqueue empty [
    now 3 |> set_priority 3;
    now 1 |> set_priority 1;
    now 2 |> set_priority 2
    ] in
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 1);
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 2);
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 3);
;;

(* recurring tasks are not lost/consumed *)
let %test_unit "sel.wait.recurring" =
  let e1 = now 1 |> set_priority 1 in
  let e2 = now 2 |> set_priority 2 |> make_recurring in
  let todo = enqueue empty [e1;e2] in
  (* 1 and 2, are ready; 2 stays there *)
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 1);
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: bool] (only_recurring_events todo) true;
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 2);
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: bool] (only_recurring_events todo) true;
  (* 2 still there *)
  let ready, todo = pop_opt todo in
  [%test_eq: int option] ready (Some 2);
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: bool] (only_recurring_events todo) true;
;;

(* recurring tasks can lead to starvation *)
let %test_unit "sel.wait.recurring.starvation" =
  let e1 = now 1 |> set_priority 1 |> make_recurring in
  let e2 = now 2 |> set_priority 2 in
  let todo = enqueue empty [e1;e2] in
  (* 1 and 2, are ready; 2 stays there *)
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: bool] (only_recurring_events todo) false;
  [%test_eq: int option] ready (Some 1);
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: int option] ready (Some 1);
  (* pp_todo (fun fmt i -> Format.fprintf fmt "%d" i) Format.std_formatter todo; *)
  [%test_eq: bool] (only_recurring_events todo) false;
;;

(* recurring tasks do not inflate the todo *)
let %test_unit "sel.wait.recurring.inflation" =
  let e1 = now 1 |> set_priority 1 |> make_recurring in
  let e2 = now 2 |> set_priority 2 |> make_recurring in
  let todo = enqueue empty [e1;e2] in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  let _, todo = pop_opt todo in
  [%test_eq: int] (size todo) 2;
;;

(* bytes n waits until n bytes are read *)
let %test_unit "sel.event.bytes" =
  let read, write = pipe () in
  let todo = enqueue empty [fst @@ on_bytes read 3 b2s] in
  (* nothing to read *)
  let ready, todo = wait_timeout todo in
  (* something to read but not enough *)
  write "1";
  let ready, todo = wait_timeout todo in
  (* more than enough *)
  write "234";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) true;
  [%test_eq: string option] ready (Some "123");
  (* extra byte is not lost *)
  [%test_eq: string] (read_leftover read 1) "4";
;;

(* internal buffer is reset *)
let %test_unit "sel.event.bytes.recurring" =
  let read, write = pipe () in
  let todo = enqueue empty [on_bytes read 3 b2s |> uncancellable |> make_recurring] in
  write "123";
let ready, todo = pop_opt todo in
  [%test_eq: string option] ready (Some "123");
  write "456";
  let ready, todo = pop_opt todo in
  [%test_eq: string option] ready (Some "456");
;;

(* queue does not run unless something is pushed *)
let%test_unit "sel.event.queue" =
  let q = Stdlib.Queue.create () in
  let todo = enqueue empty [on_queue q (fun () -> ()) |> uncancellable] in
  (* no progress since the queue is empty *)
  let ready, todo = wait_timeout todo in
  (* progress since the queue has a token *)
  Stdlib.Queue.push () q;
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (Option.is_none ready) false;
  [%test_eq: bool] (nothing_left_to_do todo) true;
;;

(* queue2 does not advance unless both queues are pushed *)
let%test_unit "sel.event.queue2" =
  let q1 = Stdlib.Queue.create () in
  let q2 = Stdlib.Queue.create () in
  let todo = enqueue empty [on_queues q1 q2 (fun () () -> ()) |> uncancellable] in
  Stdlib.Queue.push () q1;
  (* no progress since one queue is empty *)
  let ready, todo = wait_timeout todo in
  Stdlib.Queue.push () q2;
  (* progress since both queues have a token *)
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (Option.is_none ready) false;
  [%test_eq: bool] (nothing_left_to_do todo) true;
;;

(* line event waits for \n and does not eat more chars *)
let %test_unit "sel.event.line" =
  let read, write = pipe () in
  let todo = enqueue empty [on_line read s2s |> uncancellable] in
  let ready, todo = wait_timeout todo in
  write "123";
  let ready, todo = wait_timeout todo in
  write "\naa";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) true;
  [%test_eq: string option] ready (Some "123");
  [%test_eq: string] (read_leftover read 2) "aa";
;;

(* line internal buffer is not pulluted by previous run *)
let %test_unit "sel.event.line.recurring" =
  let read, write = pipe () in
  let todo = enqueue empty [on_line read s2s |> uncancellable |> make_recurring] in
  write "123\n";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "123");
  write "456\n";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "456");
;;

let %test_unit "sel.event.http_cle" =
  let read, write = pipe () in
  let todo = enqueue empty [on_httpcle read b2s |> uncancellable ] in
  write "content-Length: 4\n\n1\n3.";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) true;
  [%test_eq: string option] ready (Some "1\n3.");
;;

let %test_unit "sel.event.http_cle.recurring" =
  let read, write = pipe () in
  let todo = enqueue empty [on_httpcle read b2s |> uncancellable |> make_recurring] in
  write "content-Length: 4\n\n1\n3.";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "1\n3.");
  write "content-Length: 4\n\n4\n6.";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "4\n6.");
;;

let %test_unit "sel.event.http_cle.recurring.err" =
  let read, write = pipe () in
  let todo = enqueue empty [on_httpcle read b2s |> uncancellable |> make_recurring] in
  write "content-Length: \n";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "End_of_file");
  write "a\n";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: bool] (osmatch ".*Scan_failure.*" ready) true;
  write "content-Length: 4\n\n4\n6.";
  let ready, todo = pop_opt todo in
  [%test_eq: bool] (nothing_left_to_do todo) false;
  [%test_eq: string option] ready (Some "4\n6.");
;;

  
