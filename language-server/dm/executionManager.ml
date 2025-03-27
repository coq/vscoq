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

open Protocol
open Protocol.LspWrapper
open Scheduler
open Types

let Log log = Log.mk_log "executionManager"

type feedback_message = Feedback.level * Loc.t option * Quickfix.t list * Pp.t

type execution_status =
  | Success of Vernacstate.t option
  | Error of Pp.t Loc.located * Quickfix.t list option * Vernacstate.t option (* State to use for resiliency *)

let success vernac_st = Success (Some vernac_st)
let error loc qf msg vernac_st = Error ((loc,msg), qf, (Some vernac_st))

type sentence_id = Stateid.t

type errored_sentence = (sentence_id * Loc.t option) option

module SM = Map.Make (Stateid)

type sentence_state =
  | Done of execution_status
  | Delegated of DelegationManager.job_handle * (execution_status -> unit) option

type delegation_mode =
  | CheckProofsInMaster
  | SkipProofs
  | DelegateProofsToWorkers of { number_of_workers : int }

type options = {
  delegation_mode : delegation_mode;
  completion_options : Settings.Completion.t;
  enableDiagnostics : bool
}

let default_options = {
  delegation_mode = CheckProofsInMaster;
  completion_options = {
    enable = false;
    algorithm = StructuredSplitUnification;
    unificationLimit = 100;
    atomicFactor = 5.;
    sizeFactor = 5.
  };
  enableDiagnostics = true;
}

let doc_id = ref (-1)
let fresh_doc_id () = incr doc_id; !doc_id

type document_id = int

type coq_feedback_listener = int

type delegated_task = { 
  terminator_id: sentence_id;
  opener_id: sentence_id;
  proof_using: Vernacexpr.section_subset_expr;
  last_step_id: sentence_id option; (* only for setting a proof remotely *)
  tasks: executable_sentence list;
}

type prepared_task =
  | PSkip of { id: sentence_id; error: Pp.t option }
  | PBlock of { id: sentence_id; error: Pp.t Loc.located }
  | PExec of executable_sentence
  | PQuery of executable_sentence
  | PDelegate of delegated_task


type state = {
  initial : Vernacstate.t;
  of_sentence : (sentence_state * feedback_message list) SM.t;
  todo: prepared_task list; (* execution queue *)

  (* ugly stuff to correctly dispatch Coq feedback *)
  doc_id : document_id; (* unique number used to interface with Coq's Feedback *)
  coq_feeder : coq_feedback_listener;
  sel_feedback_queue : (Feedback.route_id * sentence_id * feedback_message) Queue.t;
  sel_cancellation_handle : Sel.Event.cancellation_handle;
  overview: exec_overview;
}

let get_id_of_executed_task task =
  match task with
  | PSkip {id} -> id
  | PBlock {id} -> id
  | PExec {id} -> id
  | PQuery {id} -> id
  | PDelegate {terminator_id} -> terminator_id

let print_exec_overview overview =
  let {processing; processed; prepared } = overview in
  log (fun () -> "--------- Prepared ranges ---------");
  List.iter (fun r -> log (fun () -> Range.to_string r)) prepared;
  log (fun () -> "-------------------------------------");
  log (fun () -> "--------- Processing ranges ---------");
  List.iter (fun r -> log (fun () -> Range.to_string r)) processing;
  log (fun () -> "-------------------------------------");
  log (fun () -> "--------- Processed ranges ---------");
  List.iter (fun r -> log (fun () -> Range.to_string r)) processed;
  log (fun () -> "-------------------------------------")


let print_exec_overview_of_state st = print_exec_overview st.overview
  
let options = ref default_options

let set_options o = options := o
let set_default_options () = options := default_options
let is_diagnostics_enabled () = !options.enableDiagnostics

let get_options () = !options

module ProofJob = struct
  type update_request =
    | UpdateExecStatus of sentence_id * execution_status
    | AppendFeedback of Feedback.route_id * Types.sentence_id * (Feedback.level * Loc.t option * Quickfix.t list * Pp.t)
  let appendFeedback (rid,sid) fb = AppendFeedback(rid,sid,fb)

  type t = {
    tasks : executable_sentence list;
    initial_vernac_state : Vernacstate.t;
    doc_id : int;
    terminator_id : sentence_id;
  }
  let name = "proof"
  let binary_name = "vscoqtop_proof_worker.opt"
  let initial_pool_size = 1

end

module ProofWorker = DelegationManager.MakeWorker(ProofJob)

type event =
  | LocalFeedback of (Feedback.route_id * sentence_id * feedback_message) Queue.t * (Feedback.route_id * sentence_id * feedback_message) list
  | ProofWorkerEvent of ProofWorker.delegation

type events = event Sel.Event.t list
let pr_event = function
  | LocalFeedback _ -> Pp.str "LocalFeedback"
  | ProofWorkerEvent event -> ProofWorker.pr_event event

let inject_proof_event = Sel.Event.map (fun x -> ProofWorkerEvent x)
let inject_proof_events st l =
  (st, List.map inject_proof_event l)

let interp_error_recovery strategy st : Vernacstate.t =
  match strategy with
  | RSkip -> st
  | RAdmitted ->
    let f = Declare.Proof.save_admitted in
    let open Vernacstate in (* shadows Declare *)
    let { Interp.lemmas; program; _ } = st.interp in
    match lemmas with
    | None -> (* if Lemma failed *)
        st
    | Some lemmas ->
        let proof = Vernacstate.LemmaStack.get_top lemmas in
        let pm = NeList.head program in
        let result = 
          try Ok(f ~pm ~proof)
          with e -> (* we also catch anomalies *)
          let e, info = Exninfo.capture e in
          Error (e, info)
        in
        match result with
        | Ok (pm) ->
          let lemmas = snd (Vernacstate.LemmaStack.pop lemmas) in
          let program = NeList.map_head (fun _ -> pm) program in
          Vernacstate.Declare.set (lemmas,program) [@ocaml.warning "-3"];
          let interp = Vernacstate.Interp.freeze_interp_state () in
          { st with interp }
        | Error (Sys.Break, _ as exn) ->
          Exninfo.iraise exn
        | Error(_,_) ->
          st

(* just a wrapper around vernac interp *)
let interp_ast ~doc_id ~state_id ~st ~error_recovery ast =
    Feedback.set_id_for_feedback doc_id state_id;
    ParTactic.set_id_for_feedback doc_id state_id;
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let result =
      try Ok(Vernacinterp.interp_entry ~st ast,[])
      with e -> (* we also catch anomalies *)
        let e, info = Exninfo.capture e in
        Error (e, info) in
    Sys.(set_signal sigint Signal_ignore);
    match result with
    | Ok (interp, events) ->
      (*
        log fun () -> "Executed: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
          " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
          *)
        let st = { st with interp } in
        st, success st, (*List.map inject_pm_event*) events
    | Error (Sys.Break, _ as exn) ->
      (*
        log (fun () -> "Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast));
        *)
        Exninfo.iraise exn
    | Error (e, info) ->
      (*
        log (fun () -> "Failed to execute: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast));
        *)
        let loc = Loc.get_loc info in
        let qf = Result.value ~default:[] @@ Quickfix.from_exception e in
        let msg = CErrors.iprint (e, info) in
        let status = error loc (Some qf) msg st in
        let st = interp_error_recovery error_recovery st in
        st, status, []

(* This adapts the Future API with our event model *)
[%%if coq = "8.18"]
let definition_using e s ~fixnames:_ ~using ~terms =
  Proof_using.definition_using e s ~using ~terms
[%%elif coq = "8.19"]
let definition_using = Proof_using.definition_using
[%%endif]

[%%if coq = "8.18" || coq = "8.19"]
let add_using proof proof_using lemmas =
      let env = Global.env () in
      let sigma, _ = Declare.Proof.get_current_context proof in
      let initial_goals pf = Proofview.initial_goals Proof.((data pf).entry) in
      let terms = List.map (fun (_,_,x) -> x) (initial_goals (Declare.Proof.get proof)) in
      let names = Vernacstate.LemmaStack.get_all_proof_names lemmas in
      let using = definition_using env sigma ~fixnames:names ~using:proof_using ~terms in
      let vars = Environ.named_context env in
      Names.Id.Set.iter (fun id ->
          if not (List.exists Util.(Context.Named.Declaration.get_id %> Names.Id.equal id) vars) then
            CErrors.user_err
              Pp.(str "Unknown variable: " ++ Names.Id.print id ++ str "."))
        using;
      let _, pstate = Declare.Proof.set_used_variables proof ~using in
      pstate
[%%else]
let add_using proof proof_using _ =
  Declare.Proof.set_proof_using proof proof_using |> snd
[%%endif]

let interp_qed_delayed ~proof_using ~state_id ~st =
  let lemmas = Option.get @@ st.Vernacstate.interp.lemmas in
  let f proof =
    let proof = add_using proof proof_using lemmas in
    let fix_exn = None in (* FIXME *)
    let f, assign = Future.create_delegate ~blocking:false ~name:"XX" fix_exn in
    Declare.Proof.close_future_proof ~feedback_id:state_id proof f, assign
  in
  let proof, assign = Vernacstate.LemmaStack.with_top lemmas ~f in
  let control = [] (* FIXME *) in
  let opaque = Vernacexpr.Opaque in
  let pending = CAst.make @@ Vernacexpr.Proved (opaque, None) in
  (*log fun () -> "calling interp_qed_delayed done";*)
  let interp = Vernacinterp.interp_qed_delayed_proof ~proof ~st ~control pending in
  (*log fun () -> "interp_qed_delayed done";*)
  let st = { st with interp } in
  st, success st, assign

let cut_overview task state document =
  let range = match task with
  | PDelegate { terminator_id } -> Document.range_of_id_with_blank_space document terminator_id
  | PSkip { id } | PExec { id } | PQuery { id } | PBlock { id } ->
    Document.range_of_id_with_blank_space document id
  in
  let {prepared; processing; processed} = state.overview in
  let prepared = RangeList.cut_from_range range prepared in
  let processing = RangeList.cut_from_range range processing in
  let overview = {prepared; processing; processed} in
  {state with overview}

let update_processed_as_Done s range overview =
  let {prepared; processing; processed} = overview in
  match s with
  | Success _ ->
    let processed = RangeList.insert_or_merge_range range processed in
    let processing = RangeList.remove_or_truncate_range range processing in
    let prepared = RangeList.remove_or_truncate_range range prepared in
    {prepared; processing; processed}
  | Error _ ->
    let processing = RangeList.remove_or_truncate_range range processing in
    let prepared = RangeList.remove_or_truncate_range range prepared in
    {prepared; processing; processed}

let update_processed id state document =
  let range = Document.range_of_id_with_blank_space document id in
  match SM.find id state.of_sentence with
  | (s, _) ->
    begin match s with
    | Done s -> 
      let overview = update_processed_as_Done s range state.overview in
      {state with overview}
    | _ -> assert false (* delegated sentences born as such, cannot become it later *)
    end
  | exception Not_found ->
    log (fun () -> "Trying to get overview with non-existing state id " ^ Stateid.to_string id);
    state

let id_of_first_task ~default = function
  | [] -> default
  | { id } :: _ -> id

let id_of_last_task ~default l =
  id_of_first_task ~default (List.rev l)

let update_processing task state document =
  let {processing; prepared} = state.overview in
  match task with
  | PDelegate { opener_id; terminator_id; tasks } ->
    let proof_opener_id = id_of_first_task ~default:opener_id tasks in
    let proof_closer_id = id_of_last_task ~default:terminator_id tasks in
    let proof_begin_range = Document.range_of_id_with_blank_space document proof_opener_id in
    let proof_end_range = Document.range_of_id_with_blank_space document proof_closer_id in
    let range = Range.create ~end_:proof_end_range.end_ ~start:proof_begin_range.start in
    (* When a job is delegated we shouldn't merge ranges (to get the proper progress report) *)
    let processing = List.append processing [ range ] in 
    let prepared = RangeList.remove_or_truncate_range range prepared in
    let overview = {state.overview with prepared; processing} in
    {state with overview}
  | PSkip { id } | PExec { id } | PQuery { id } | PBlock { id } ->
    let range = Document.range_of_id_with_blank_space document id in
    let processing = RangeList.insert_or_merge_range range processing in
    let prepared = RangeList.remove_or_truncate_range range prepared in
    let overview = {state.overview with processing; prepared} in
    {state with overview}

let update_prepared task document state =
  let {prepared} = state.overview in
  match task with
  | PDelegate { opener_id; terminator_id; tasks } ->
    let proof_opener_id = id_of_first_task ~default:opener_id tasks in
    let proof_closer_id = id_of_last_task ~default:terminator_id tasks in
    let proof_begin_range = Document.range_of_id_with_blank_space document proof_opener_id in
    let proof_end_range = Document.range_of_id_with_blank_space document proof_closer_id in
    let range = Range.create ~end_:proof_end_range.end_ ~start:proof_begin_range.start in
    (* When a job is delegated we shouldn't merge ranges (to get the proper progress report) *)
    let prepared = List.append prepared [ range ] in
    let overview = {state.overview with prepared} in
    {state with overview}
  | PSkip { id } | PExec { id } | PQuery { id } | PBlock { id } ->
    let range = Document.range_of_id_with_blank_space document id in
    let prepared = RangeList.insert_or_merge_range range prepared in
    let overview = {state.overview with prepared} in
    {state with overview}

let update_overview task state document =
  let state = 
  match task with
  | PDelegate { terminator_id } ->
    let range = Document.range_of_id_with_blank_space document terminator_id in
    let {prepared} = state.overview in
    let prepared = RangeList.remove_or_truncate_range range prepared in
    let overview = update_processed_as_Done (Success None) range state.overview in
    let overview = {overview with prepared} in
    {state with overview}
  | PSkip { id } | PExec { id } | PQuery { id } | PBlock { id } ->
    update_processed id state document
  in
  match state.todo with
  | [] -> state
  | next :: _ -> update_processing next state document


let build_prepared_overview state document =
  List.fold_right (fun task st -> update_prepared task document st) state.todo state

let build_processed_overview state document =
  let sentence_ids = SM.bindings state.of_sentence in
  let sentence_ids = List.map (fun x -> fst x) sentence_ids in
  List.fold_right (fun id st -> update_processed id st document) sentence_ids state

let reset_overview st document =
  let overview = {processed=[]; prepared=[]; processing=[]} in
  let st = build_processed_overview {st with overview} document in
  build_prepared_overview st document

let prepare_overview st prepared =
  let overview = {st.overview with prepared} in
  {st with overview}

let overview st = st.overview

let overview_until_range st range =
  let find_final_range l = List.find_opt (fun (r: Range.t) -> Range.included ~in_:r range) l in
  let {processed; processing; prepared} = st.overview in
  let final_range = find_final_range processed  in
  match final_range with
  | None ->
    let final_range = find_final_range processing in
    begin match final_range with
    | None -> { processed; processing; prepared }
    | Some { start } ->
      let processing = (List.filter (fun (r: Range.t) -> not @@ Range.included ~in_:r range) processing) in
      let processing = List.append processing [Range.create ~start:start ~end_:range.end_] in
      {processing; processed; prepared}
    end
  | Some { start } ->
    let processed = (List.filter (fun (r: Range.t) -> (not @@ Range.included ~in_:r range) && (Position.compare r.start range.end_ <= 0)) processed) in
    let processed = List.append processed [Range.create ~start:start ~end_:range.end_] in
    print_exec_overview {processing; processed;prepared};
    { processing; processed; prepared }


let update_all id v fl state =
  { state with of_sentence = SM.add id (v, fl) state.of_sentence }
;;
let update state id v =
  let fl = try snd (SM.find id state.of_sentence) with Not_found -> [] in
  update_all id (Done v) fl state
;;

let local_feedback feedback_queue : event Sel.Event.t =
  Sel.On.queue_all ~name:"feedback" ~priority:PriorityManager.feedback feedback_queue (fun x xs -> LocalFeedback(feedback_queue, x :: xs))

let install_feedback_listener doc_id send =
  Log.feedback_add_feeder_on_Message (fun route span doc lvl loc qf msg ->
    if lvl != Feedback.Debug && doc = doc_id then send (route,span,(lvl,loc, qf, msg)))

let init vernac_state =
  let doc_id = fresh_doc_id () in
  let sel_feedback_queue = Queue.create () in
  let coq_feeder = install_feedback_listener doc_id (fun x -> Queue.push x sel_feedback_queue) in
  let event = local_feedback sel_feedback_queue in
  let sel_cancellation_handle = Sel.Event.get_cancellation_handle event in
  {
    initial = vernac_state;
    of_sentence = SM.empty;
    todo = [];
    doc_id;
    coq_feeder;
    sel_feedback_queue;
    sel_cancellation_handle;
    overview = empty_overview;
  },
  event

(* called by the forked child. Since the Feedback API is imperative, the
   feedback pipes have to be modified in place *)
let feedback_cleanup { coq_feeder; sel_feedback_queue; sel_cancellation_handle } =
  Feedback.del_feeder coq_feeder;
  Queue.clear sel_feedback_queue;
  Sel.Event.cancel sel_cancellation_handle

let handle_feedback state (_,id, fb) =
  match fb with
  | (_, _, _, msg) ->
    begin match SM.find id state.of_sentence with
    | (s,fl) -> update_all id s (fl @ [fb]) state
    | exception Not_found -> 
        log (fun () -> "Received feedback on non-existing state id " ^ Stateid.to_string id ^ ": " ^ Pp.string_of_ppcmds msg);
        state
    end 

let handle_event event state =
  match event with
  | LocalFeedback (q,l) ->
      None, Some (List.fold_left handle_feedback state l), [local_feedback q]
  | ProofWorkerEvent event ->
      let update, events = ProofWorker.handle_event event in
      let state, id =
        match update with
        | None -> None, None
        | Some (ProofJob.AppendFeedback(x,id,fb)) ->
            Some (handle_feedback state (x,id,fb)), None
        | Some (ProofJob.UpdateExecStatus(id,v)) ->
            match SM.find id state.of_sentence, v with
            | (Delegated (_,completion), fl), _ ->
                Option.default ignore completion v;
                Some (update_all id (Done v) fl state), Some id
            | (Done (Success s), fl), Error (err,qf, _) ->
                (* This only happens when a Qed closing a delegated proof
                   receives an updated by a worker saying that the proof is
                   not completed *)
                Some (update_all id (Done (Error (err,qf,s))) fl state), Some id
            | (Done _, _), _ -> None, Some id
            | exception Not_found -> None, None (* TODO: is this possible? *)
      in
      let state, events = inject_proof_events state events in
      id, state, events

let find_fulfilled_opt x m =
  try
    let ss,_ = SM.find x m in
    match ss with
    | Done x -> Some x
    | Delegated _ -> None
  with Not_found -> None


let exec_error_of_execution_status id v = match v with
  | Success _ -> None
  | Error ((loc, _), _, _) -> Some (id, loc)

let get_vs_and_exec_error st id =
  match fst @@ SM.find id st.of_sentence with
  | Done (Success (Some vs) as es) -> vs, exec_error_of_execution_status id es
  | Done (Error (_,_,Some vs) as es) -> vs, exec_error_of_execution_status id es
  | _ -> CErrors.anomaly Pp.(str "get_vs_and_exec_error call should be protected with is_locally_executed")
  | exception Not_found -> assert false

let is_locally_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success (Some _) | Error (_,_,Some _)) -> true
  | _ -> false

let is_remotely_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success None | Error (_,_,None)) -> true
  | _ -> false
  
  
let jobs : (DelegationManager.job_handle * Sel.Event.cancellation_handle * ProofJob.t) Queue.t = Queue.create ()

(* TODO: kill all Delegated... *)
let destroy st =
  feedback_cleanup st;
  Queue.iter (fun (h,c,_) -> DelegationManager.cancel_job h; Sel.Event.cancel c) jobs


let last_opt l = try Some (CList.last l).id with Failure _ -> None

let prepare_task task : prepared_task list =
  match task with
  | Skip { id; error } -> [PSkip { id; error }]
  | Block { id; error } -> [PBlock {id; error}]
  | Exec e -> [PExec e]
  | Query e -> [PQuery e]
  | OpaqueProof { terminator; opener_id; tasks; proof_using} ->
      match !options.delegation_mode with
      | DelegateProofsToWorkers _ ->
          log (fun () -> "delegating proofs to workers");
          let last_step_id = last_opt tasks in
          [PDelegate {terminator_id = terminator.id; opener_id; last_step_id; tasks; proof_using}]
      | CheckProofsInMaster ->
          log (fun () -> "running the proof in master as per config");
          List.map (fun x -> PExec x) tasks @ [PExec terminator]
      | SkipProofs ->
          log (fun () -> Printf.sprintf "skipping proof made of %d tasks" (List.length tasks));
          [PExec terminator]

let id_of_prepared_task = function
  | PSkip { id } -> id
  | PBlock { id } -> id
  | PExec ex -> ex.id
  | PQuery ex -> ex.id
  | PDelegate { terminator_id } -> terminator_id

let purge_state = function
  | Success _ -> Success None
  | Error(e,_,_) -> Error (e,None,None)

(* TODO move to proper place *)
let worker_execute ~doc_id ~send_back (vs,events) { id; ast; synterp; error_recovery } =
  let vs = { vs with Vernacstate.synterp } in
  log (fun () -> "worker interp " ^ Stateid.to_string id);
  let vs, v, ev = interp_ast ~doc_id ~state_id:id ~st:vs ~error_recovery ast in
  send_back (ProofJob.UpdateExecStatus (id,purge_state v));
  (vs, events @ ev)

(* The execution of Qed for a non-delegated proof checks the proof is completed.
   When the proof is delegated this step is performed by the worker, which
   sends back an update on the Qed sentence in case the proof is unfinished *)
let worker_ensure_proof_is_over vs send_back terminator_id =
  let f = Declare.Proof.close_proof in
  let open Vernacstate in (* shadows Declare *)
  let { Interp.lemmas } = vs.interp in
  match lemmas with
  | None -> assert false
  | Some lemmas ->
      let proof = Vernacstate.LemmaStack.get_top lemmas in
      try let _ = f ~opaque:Vernacexpr.Opaque ~keep_body_ucst_separate:false proof in ()
      with e ->
        let e, info = Exninfo.capture e in
        let loc = Loc.get_loc info in
        let qf = Result.value ~default:[] @@ Quickfix.from_exception e in
        let msg = CErrors.iprint (e, info) in
        let status = error loc (Some qf) msg vs in
        send_back (ProofJob.UpdateExecStatus (terminator_id,status))

let worker_main { ProofJob.tasks; initial_vernac_state = vs; doc_id; terminator_id } ~send_back =
  try
    let vs, _ = List.fold_left (worker_execute ~doc_id ~send_back) (vs,[]) tasks in
    worker_ensure_proof_is_over vs send_back terminator_id;
    flush_all ();
    exit 0
  with e ->
    let e, info = Exninfo.capture e in
    let message = CErrors.iprint_no_report (e, info) in
    Feedback.msg_debug @@ Pp.str "======================= worker ===========================";
    Feedback.msg_debug message;
    Feedback.msg_debug @@ Pp.str "==========================================================";
    exit 1

let execute_task st (vs, events, interrupted) task =
  if interrupted then begin
    let st = update st (id_of_prepared_task task) (Error ((None,Pp.str "interrupted"),None,None)) in
    let todo = [] in
    ({st with todo}, vs, events, true, None)
  end else
    try
      match task with
      | PBlock { id; error = err} ->
        let (loc, pp) = err in
        let v = error loc None pp vs in
        let parse_error = Some (id, loc) in
        let st = update st id v in
        (st, vs, events, false, parse_error)
      | PSkip { id; error = err } ->
          let v = match err with
            | None -> success vs
            | Some msg -> error None None msg vs
          in
          let st = update st id v in
          (st, vs, events, false, None)
      | PExec { id; ast; synterp; error_recovery } ->
          let vs = { vs with Vernacstate.synterp } in
          let vs, st, ev, exec_error =
            if is_locally_executed st id then
              let vs, exec_error = get_vs_and_exec_error st id in
              log (fun () -> Format.asprintf "skipping execution of already executed %s" (Stateid.to_string id));
              vs, st, [], exec_error
            else
              let vs, v, ev = interp_ast ~doc_id:st.doc_id ~state_id:id ~st:vs ~error_recovery ast in
              let st = update st id v in
              let exec_error = exec_error_of_execution_status id v in
              vs, st, ev, exec_error
          in
          (st, vs, events @ ev, false, exec_error)
      | PQuery { id; ast; synterp; error_recovery } ->
          let vs = { vs with Vernacstate.synterp } in
          let _, v, ev = interp_ast ~doc_id:st.doc_id ~state_id:id ~st:vs ~error_recovery ast in
          let st = update st id v in
          (st, vs, events @ ev, false, None)
      | PDelegate { terminator_id; opener_id; last_step_id; tasks; proof_using } ->
          begin match find_fulfilled_opt opener_id st.of_sentence with
          | Some (Success _) ->
            let job =  { ProofJob.tasks; initial_vernac_state = vs; doc_id = st.doc_id; terminator_id } in
            let job_id = DelegationManager.mk_job_handle (0,terminator_id) in
            (* The proof was successfully opened *)
            let last_vs, _v, assign = interp_qed_delayed ~state_id:terminator_id ~proof_using ~st:vs in
            let complete_job status =
              try match status with
              | Success None ->
                log (fun () -> "Resolved future (without sending back the witness)");
                assign (`Exn (Failure "no proof",Exninfo.null))
              | Success (Some vernac_st) ->
                let f proof =
                  log (fun () -> "Resolved future");
                  assign (`Val (Declare.Proof.return_proof proof))
                in
                Vernacstate.LemmaStack.with_top (Option.get @@ vernac_st.Vernacstate.interp.lemmas) ~f
              | Error ((loc,err),_,_) ->
                  log (fun () -> "Aborted future");
                  assign (`Exn (CErrors.UserError err, Option.fold_left Loc.add_loc Exninfo.null loc))
              with exn when CErrors.noncritical exn ->
                assign (`Exn (CErrors.UserError(Pp.str "error closing proof"), Exninfo.null))
            in
            let st = update st terminator_id (success last_vs) in
            let st = List.fold_left (fun st id ->
               if Option.equal Stateid.equal (Some id) last_step_id then
                 update_all id (Delegated (job_id,Some complete_job)) [] st
               else
                 update_all id (Delegated (job_id,None)) [] st)
               st (List.map (fun { id } -> id) tasks) in
            let e =
                ProofWorker.worker_available ~jobs
                  ~fork_action:worker_main
                  ~feedback_cleanup:(fun () -> feedback_cleanup st)
                in
              Queue.push (job_id, Sel.Event.get_cancellation_handle e, job) jobs;
              (st, last_vs,events @ [inject_proof_event e] ,false, None)
          | _ ->
            (* If executing the proof opener failed, we skip the proof *)
            let st = update st terminator_id (success vs) in
            (st, vs,events,false, None)
          end
    with Sys.Break ->
      let st = update st (id_of_prepared_task task) (Error ((None,Pp.str "interrupted"),None,None)) in
      (st, vs, events, true, None)

let execute st document (vs, events, interrupted) task block_on_first_error =
  let st, vst_for_next_todo, events, _, exec_error =
    execute_task st (vs, events, interrupted) task in
  match block_on_first_error, exec_error with
  | false, _ | _, None ->
    let st = update_overview task st document in
    let next, st = match st.todo with
      | [] -> None, st
      | task :: todo -> Some task, { st with todo }
    in next, st, vst_for_next_todo, events, None
  | true, Some _ ->
    let st = cut_overview task st document in
    let st = { st with todo=[]} in
    None, st, vst_for_next_todo, events, exec_error

let execute_with_no_overview st (vs, events, interrupted) task block_on_first_error =
  let st, vst_for_next_todo, events, _, exec_error =
    execute_task st (vs, events, interrupted) task in
  match block_on_first_error, exec_error with
  | false, _ | _, None ->
    let next, st = match st.todo with
      | [] -> None, st
      | task :: todo -> Some task, { st with todo }
    in next, st, vst_for_next_todo, events, None
  | true, Some _ ->
    let st = { st with todo=[]} in
    None, st, vst_for_next_todo, events, exec_error


let build_tasks_for document sch st id block =
  let rec build_tasks id tasks st =
    begin match find_fulfilled_opt id st.of_sentence with
    | Some (Success (Some vs)) ->
      (* We reached an already computed state *)
      log (fun () -> "Reached computed state " ^ Stateid.to_string id);
      vs, tasks, st, None
    | Some (Error((loc, _),_,Some vs)) ->
      (* We try to be resilient to an error *)
      log (fun () -> "Error resiliency on state " ^ Stateid.to_string id);
      vs, tasks, st, Some (id, loc)
    | _ ->
      log (fun () -> "Non (locally) computed state " ^ Stateid.to_string id);
      let (base_id, task) = task_for_sentence sch id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        st.initial, task :: tasks, st, None
      | Some base_id ->
        build_tasks base_id (task::tasks) st
      end
    end
  in
  let rec build_prepared_overview tasks state =
    begin match tasks with
    | [] -> state
    | task :: l -> build_prepared_overview l (update_prepared task document state)
    end
  in
  let vs, tasks, st, error_id = build_tasks id [] st in
  match error_id, block with
  | _, false | None, _ ->
    let todo = List.concat_map prepare_task tasks in
    let task, st = match todo with
      | task :: todo ->
        let st = {st with todo} in
        let st = build_prepared_overview todo st in
        Some task, st
      | [] ->
        None, {st with todo}
      in
      vs, st, task, None
  | Some id, true ->
    vs, {st with todo=[]}, None, Some id

let build_tasks_for_sentences st sch sentences =
  let tasks = List.map (fun ({id}: Document.sentence) -> snd @@ task_for_sentence sch id) sentences in
  let todo = List.concat_map prepare_task tasks in
  match todo with
  | task :: todo ->
    Some task, {st with todo}
  | [] -> None, st

let all_errors st =
  List.fold_left (fun acc (id, (p,_)) ->
    match p with
    | Done (Error ((loc,e),qf,_)) -> (id,(loc,e,qf)) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.of_sentence

let error st id =
  match SM.find_opt id st.of_sentence with
  | Some (Done (Error (err,_,_)), _) -> Some err
  | _ -> None

let feedback st id =
  match SM.find_opt id st.of_sentence with
  | None -> []
  | Some (_st, l) -> l

let all_feedback st =
  List.fold_left (fun acc (id, (_,l)) -> List.map (fun x -> (id, x)) l @ acc) [] @@ SM.bindings st.of_sentence

let shift_overview st ~before ~after ~start ~offset =
  let shift_loc loc_start loc_end =
    if loc_start >= start then (loc_start + offset, loc_end + offset)
    else if loc_end > start then (loc_start, loc_end + offset)
    else (loc_start, loc_end)
  in
  let shift_range range =
    let r_start = RawDocument.loc_of_position before range.Range.start in
    let r_stop = RawDocument.loc_of_position before range.Range.end_ in
    let r_start', r_stop' = shift_loc r_start r_stop in
    Range.create ~start:(RawDocument.position_of_loc after r_start') ~end_:(RawDocument.position_of_loc after r_stop')
  in
  let processed = CList.Smart.map shift_range st.overview.processed in
  let processing = CList.Smart.map shift_range st.overview.processing in
  let prepared = CList.Smart.map shift_range st.overview.prepared in
  let overview = {processed; processing; prepared} in
  {st with overview}

let shift_diagnostics_locs st ~start ~offset =
  let shift_loc loc =
    let (loc_start, loc_stop) = Loc.unloc loc in
    if loc_start >= start then Loc.shift_loc offset offset loc
    else if loc_stop > start then Loc.shift_loc 0 offset loc
    else loc
  in
  let shift_feedback (level, oloc, qf, msg as feedback) =
    match oloc with
    | None -> feedback
    | Some loc ->
      let loc' = shift_loc loc in
      if loc' == loc then feedback else (level, Some loc', qf, msg)
  in
  let shift_error (sentence_state, feedbacks as orig) =
    let sentence_state' = match sentence_state with
      | Done (Error ((Some loc,e),qf,st)) ->
        let loc' = shift_loc loc in
        if loc' == loc then sentence_state else
        Done (Error ((Some loc',e),qf,st))
      | _ -> sentence_state
    in
    let feedbacks' = CList.Smart.map shift_feedback feedbacks in
    if sentence_state' == sentence_state && feedbacks' == feedbacks then orig else
    (sentence_state', feedbacks')
  in
  { st with of_sentence = SM.map shift_error st.of_sentence }

let executed_ids st =
  SM.fold (fun id (p,_) acc ->
    match p with
    | Done _ -> id :: acc
    | _ -> acc) st.of_sentence []

let invalidate1 of_sentence id =
  try
    let p,_ = SM.find id of_sentence in
    match p with
    | Delegated (job_id,_) ->
        DelegationManager.cancel_job job_id;
        SM.remove id of_sentence
    | _ -> SM.remove id of_sentence
  with Not_found -> of_sentence

let cancel1 todo invalid_id =
  let task_of_id = function
    | PSkip { id } | PExec { id } | PQuery { id } | PBlock { id } -> Stateid.equal id invalid_id
    | PDelegate _ -> false
  in
  List.filter task_of_id todo

let rec invalidate document schedule id st =
  log (fun () -> "Invalidating: " ^ Stateid.to_string id);
  let of_sentence = invalidate1 st.of_sentence id in
  let todo = cancel1 st.todo id in
  let old_jobs = Queue.copy jobs in
  let removed = ref [] in
  Queue.clear jobs;
  Queue.iter (fun ((_, cancellation, { ProofJob.terminator_id; tasks }) as job) ->
    if terminator_id != id then
      Queue.push job jobs
    else begin
      Sel.Event.cancel cancellation;
      removed := List.map (fun e -> PExec e) tasks :: !removed
    end) old_jobs;
  let of_sentence = List.fold_left invalidate1 of_sentence
    List.(concat (map (fun tasks -> map id_of_prepared_task tasks) !removed)) in
  if of_sentence == st.of_sentence then st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (invalidate document schedule) deps { st with of_sentence; todo }

let context_of_state st =
    Vernacstate.Interp.unfreeze_interp_state st;
    begin match st.lemmas with
    | None ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      sigma, env
    | Some lemmas ->
      let open Declare in
      let open Vernacstate in
      lemmas |> LemmaStack.with_top ~f:Proof.get_current_context
    end

let get_context st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log (fun () -> "Cannot find state for get_context"); None
  | Some (Error _) -> log (fun () -> "Context requested in error state"); None
  | Some (Success None) -> log (fun () -> "Context requested in a remotely checked state"); None
  | Some (Success (Some { interp = st })) ->
    Some (context_of_state st)

let get_initial_context st =
  context_of_state st.initial.Vernacstate.interp

let get_vernac_state st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log (fun () -> "Cannot find state for get_context"); None
  | Some (Error (_,_,None)) -> log (fun () -> "State requested after error with no state"); None
  | Some (Success None) -> log (fun () -> "State requested in a remotely checked state"); None
  | Some (Success (Some st))
  | Some (Error (_,_, Some st)) ->
    Some st

module ProofWorkerProcess = struct
  type options = ProofWorker.options
  let parse_options = ProofWorker.parse_options
  let main ~st:_ options =
    let send_back, job = ProofWorker.setup_plumbing options in
    worker_main job ~send_back
  let log = ProofWorker.log
end

