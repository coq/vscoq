(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


let debug_delegation_manager = CDebug.create ~name:"vscoq.delegationManager" ()

let log msg = debug_delegation_manager Pp.(fun () ->
  str @@ Format.asprintf "[%d] %s" (Unix.getpid ()) msg)

type sentence_id = Stateid.t

type link = {
  write_to :  Unix.file_descr;
  read_from:  Unix.file_descr;
}

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

let write_value { write_to; _ } x =
  let data = Marshal.to_bytes x [] in
  let datalength = Bytes.length data in
  log @@ Printf.sprintf "marshaling %d bytes" datalength;
  let writeno = Unix.write write_to data 0 datalength in
  assert(writeno = datalength);
  log @@ Printf.sprintf "marshaling done";
  flush_all ()

let abort_on_unix_error f x =
  try
    f x
  with Unix.Unix_error(e,f,p) ->
    Printf.eprintf "Error: %s: %s: %s\n%!" f p (Unix.error_message e);
    exit 3

module type Job = sig
  type t
  val name : string
  val binary_name : string
  val pool_size : int
  type update_request
  val appendFeedback : sentence_id -> (Feedback.level * Loc.t option * Pp.t) -> update_request
end

(* One typically created a job id way before the worker is spawned, so we
   allocate a slot for the PID, but set it later. The sentence_id is used
   for error reporting (e.g. fail to spawn) *)
type job_id = sentence_id * int option ref
let mk_job_id sid = sid, ref None
let cancel_job (_,id) =
  match !id with
  | None -> ()
  | Some pid -> Unix.kill pid 9

(* TODO: this queue should not be here, it should be "per URI" but we want to
   keep here the conversion (STM) feedback -> (LSP) feedback *)
let master_feedback_queue = Queue.create ()

let install_feedback send =
  Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    | Feedback.Message(Feedback.Debug,loc,m) ->
        (* This is crucial to avoid a busy loop: since a feedback triggers and
           event, if SEL debug is on we loop, since processing the debug print
           is also a feedback *)
        Printf.eprintf "%s\n" @@ Pp.string_of_ppcmds m
    | Feedback.Message(lvl,loc,m) -> send (fb.Feedback.span_id,(lvl,loc,m))
    | Feedback.AddedAxiom -> send (fb.Feedback.span_id,(Feedback.Warning,None,Pp.str "axiom added"))
    | _ -> () (* STM feedbacks are handled differently *))

let master_feeder = install_feedback (fun x -> Queue.push x master_feedback_queue)

let local_feedback : (sentence_id * (Feedback.level * Loc.t option * Pp.t)) Sel.event =
  Sel.on_queue master_feedback_queue (fun x -> x)

module MakeWorker (Job : Job) = struct

let debug_worker = CDebug.create ~name:("vscoq.Worker." ^ Job.name) ()

let log_worker msg = debug_worker Pp.(fun () ->
  str @@ Format.asprintf "    [%d] %s" (Unix.getpid ()) msg)

let install_feedback_worker link =
  Feedback.del_feeder master_feeder;
  ignore(install_feedback (fun (id,fb) -> write_value link (Job.appendFeedback id fb)))

(* This is the lifetime of a delegation, there is one start event, many progress
   evants, then one ending event. *)
type delegation =
 | WorkerStart : job_id * 'job * ('job -> send_back:(Job.update_request -> unit) -> unit) * string -> delegation
 | WorkerProgress of { link : link; update_request : Job.update_request }
 | WorkerEnd of (int * Unix.process_status)
 | WorkerIOError of exn
let pr_event = function
  | WorkerEnd _ -> Pp.str "WorkerEnd"
  | WorkerIOError _ -> Pp.str "WorkerIOError"
  | WorkerProgress _ -> Pp.str "WorkerProgress"
  | WorkerStart _ -> Pp.str "WorkerStart"

type events = delegation Sel.event list

type role = Master | Worker of link

(* The pool is just a queue of tokens *)
let pool = Queue.create ()
let () = for _i = 0 to Job.pool_size do Queue.push () pool done

(* In order to create a job we enqueue this event *)
let worker_available ~jobs ~fork_action : delegation Sel.event =
  Sel.on_queues jobs pool (fun (job_id, job) () ->
    WorkerStart (job_id,job,fork_action,Job.binary_name))

(* When a worker is spawn, we enqueue this event, since eventually it will die *)
let worker_ends pid : delegation Sel.event =
  Sel.on_death_of ~pid (fun reason -> WorkerEnd(pid,reason))

(* When a worker is spawn, we enqueue this event, since eventually will make progress *)
let worker_progress link : delegation Sel.event =
  Sel.on_ocaml_value link.read_from (function
    | Error e -> WorkerIOError e
    | Ok update_request -> WorkerProgress { link; update_request; })

(* ************ spawning *************************************************** *)

let accept_timeout ?(timeout=2.0) sr =
  let r, _, _ = Unix.select [sr] [] [] timeout in
  if r = [] then None
  else Some (Unix.accept sr)

let fork_worker : job_id -> (role * events, string * events) result = fun (_, job_id) ->
  let open Unix in
  try
    let chan = socket PF_INET SOCK_STREAM 0 in
    bind chan (ADDR_INET (Unix.inet_addr_loopback,0));
    listen chan 1;
    let address = getsockname chan in
    log @@ "forking...";
    flush_all ();
    let null = openfile "/dev/null" [O_RDWR] 0o640 in
    let pid = fork () in
    if pid = 0 then begin
        (* Children process *)
        dup2 null stdin;
        close chan;
        log_worker @@ "borning...";
        let chan = socket PF_INET SOCK_STREAM 0 in
        connect chan address;
        let read_from = chan in
        let write_to = chan in
        let link = { write_to; read_from } in
        install_feedback_worker link;
        Ok (Worker link, [])
    end else
      (* Parent process *)
      let () = job_id := Some pid in
      match accept_timeout chan with
      | None ->
          close chan;
          log @@ Printf.sprintf "forked pid %d did not connect back" pid;
          Unix.kill pid 9;
          Error ("worker did not connect back", [worker_ends pid])
      | Some (worker, _worker_addr) ->
          close chan;
          log @@ Printf.sprintf "forked pid %d called back" pid;
          let read_from = worker in
          let write_to = worker in
          let link = { write_to; read_from } in
          Ok (Master, [worker_progress link; worker_ends pid])
  with Unix_error(e,f,p) ->
    Error (f ^": "^ p^": " ^error_message e,[])

;;

let option_name = "-" ^ Str.global_replace (Str.regexp_string " ") "." Job.name ^ "_master_address"

let create_process_worker procname (_,job_id) job =
  let open Unix in
  try
    let chan = socket PF_INET SOCK_STREAM 0 in
    bind chan (ADDR_INET (Unix.inet_addr_loopback,0));
    listen chan 1;
    let port = match getsockname chan with
      | ADDR_INET(_,port) -> port
      | _ -> assert false in
    let null = openfile "/dev/null" [O_RDWR] 0o640 in
    let extra_flags = if CDebug.get_flags () = "all" then [|"-debug"|] else [||] in
    let args = Array.append  [|procname;option_name;string_of_int port|] extra_flags in
    let pid = create_process procname args null stdout stderr in
    close null;
    let () = job_id := Some pid in
    log @@ Printf.sprintf "created worker %d, waiting on port %d" pid port;
    match accept_timeout chan with
    | Some(worker, _worker_addr) ->
        close chan;
        let read_from = worker in
        let write_to = worker in
        let link = { write_to; read_from } in
        install_feedback_worker link;
        log @@ "sending job";
        write_value link job;
        flush_all ();
        log @@ "sent";
        Ok [worker_progress link; worker_ends pid]
    | None ->
        log @@ Printf.sprintf "child process %d did not connect back" pid;
        Unix.kill pid 9;
        Error ("worker did not connect back", [worker_ends pid])
  with Unix_error(e,f,p) ->
    Error (f ^": "^ p^": " ^error_message e,[])


(* **************** /spawning ********************************************** *)

let handle_event = function
  | WorkerIOError e ->
     log @@ "worker IO Error: " ^ Printexc.to_string e;
     (None, [])
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "worker %d went on holidays" pid;
      Queue.push () pool;
      (None,[])
  | WorkerProgress { link; update_request } ->
      log "worker progress";
      (Some update_request, [worker_progress link])
  | WorkerStart (job_id,job,action,procname) ->
    log "worker starts";
    if Sys.os_type = "Unix" then
      match fork_worker job_id with
      | Ok(Master, events) ->
        log "worker spawned (fork)";
        (None, events)
      | Ok(Worker link, _) ->
        action job ~send_back:(abort_on_unix_error write_value link);
        exit 0
      | Error(msg, cleanup_events) ->
        log @@ "worker did not spawn: " ^ msg;
        (Some(Job.appendFeedback (fst job_id) (Feedback.Error,None,Pp.str msg)), cleanup_events)
    else
      match create_process_worker procname job_id job with
      | Ok events ->
          log "worker spawned (create_process)";
          (None, events)
      | Error(msg, cleanup_events) ->
          log @@ "worker did not spawn: " ^ msg;
          (Some(Job.appendFeedback (fst job_id) (Feedback.Error,None,Pp.str msg)), cleanup_events)


(* the only option is the socket port *)
type options = int

let setup_plumbing port =
  try
    let open Unix in
    let chan = socket PF_INET SOCK_STREAM 0 in
    let address = ADDR_INET (inet_addr_loopback,port) in
    log_worker @@ "connecting to " ^ string_of_int port;
    connect chan address;
    let read_from = chan in
    let write_to = chan in
    let link = { read_from; write_to } in
    (* Unix.read_value does not exist, we use Sel *)
    match Sel.wait [Sel.on_ocaml_value read_from (fun x -> x)] with
    | [Ok (job : Job.t)], _ -> (write_value link, job)
    | [Error exn], _ ->
      log_worker @@ "error receiving job: " ^ Printexc.to_string exn;
      exit 1
    | _ -> assert false
  with Unix.Unix_error(code,syscall,param) ->
    log_worker @@ Printf.sprintf "error starting: %s: %s: %s" syscall param (Unix.error_message code);
    exit 1

let parse_options extra_args =
  match extra_args with
  | [ o ; port ] when o = option_name -> int_of_string port, []
  | _ ->
    Printf.eprintf "unknown arguments: %s" (String.concat " " extra_args);
    exit 2

let log = log_worker

end
