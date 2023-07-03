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

let lsp_initialization_done = ref false
let initialization_feedback_queue = Queue.create ()

let init_log =
  try Some (
    let oc = open_out @@ Filename.temp_file "vscoq_init_log." ".txt" in
    output_string oc "command line:\n";
    output_string oc (String.concat " " (Sys.argv |> Array.to_list));
    output_string oc "\nstatic initialization:\n";
    oc)
  with _ -> None

let write_to_init_log str =
  Option.iter (fun oc ->
      output_string oc str;
      output_char oc '\n';
      flush oc)
    init_log

let rec is_enabled name = function
  | [] -> false
  | "-vscoq-d" :: "all" :: _ -> true
  | "-vscoq-d" :: v :: rest ->
    List.mem name (String.split_on_char ',' v) || is_enabled name rest
  | _ :: rest -> is_enabled name rest

let logs = ref []

let handle_event s = Printf.eprintf "%s\n" s

let mk_log name =
  logs := name :: !logs;
  let flag = is_enabled name (Array.to_list Sys.argv) in
  let flag_init = is_enabled "init" (Array.to_list Sys.argv) in
  write_to_init_log ("log " ^ name ^ " is " ^ if flag then "on" else "off");
  Log (fun msg ->
    let should_print_log = flag || (flag_init && not !lsp_initialization_done) in
    if should_print_log then begin
      let txt = Format.asprintf "[%-20s, %d, %f] %s" name (Unix.getpid ()) (Unix.gettimeofday ()) msg in
      if not !lsp_initialization_done then begin
        write_to_init_log txt;
        Queue.push txt initialization_feedback_queue (* Emission must be delayed as per LSP spec *)
      end else
        handle_event txt
    end else
      ())

let logs () = List.sort String.compare !logs

type event = string
type events = event Sel.Event.t list

let install_debug_feedback f =
  Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    | Feedback.Message(Feedback.Debug,None,m) -> f Pp.(string_of_ppcmds m)
    | _ -> ())

(* We go through a queue in case we receive a debug feedback from Coq before we
   replied to Initialize *)
let coq_debug_feedback_queue = Queue.create ()
let main_debug_feeder = install_debug_feedback (fun txt -> Queue.push txt coq_debug_feedback_queue)
   
let debug : event Sel.Event.t =
  Sel.On.queue ~name:"debug" ~priority:PriorityManager.feedback coq_debug_feedback_queue (fun x -> x)
let cancel_debug_event = Sel.Event.get_cancellation_handle debug

let lsp_initialization_done () =
  lsp_initialization_done := true;
  Option.iter close_out_noerr init_log;
  Queue.iter handle_event initialization_feedback_queue;
  Queue.clear initialization_feedback_queue;
  [debug]

let worker_initialization_begins () =
  Sel.Event.cancel cancel_debug_event;
  Feedback.del_feeder main_debug_feeder;
    (* We do not want to inherit master's Feedback reader (feeder), otherwise we
    would output on the worker's stderr.
    Debug feedback from worker is forwarded to master via a specific handler
    (see [worker_initialization_done]) *)
  Queue.clear coq_debug_feedback_queue

let worker_initialization_done ~fwd_event =
  let _ = install_debug_feedback fwd_event in
  ()
