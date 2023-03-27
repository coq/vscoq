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

open Scheduler
open Types

let Log log = Log.mk_log "executionManager"

type execution_status = DelegationManager.execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

let success vernac_st = Success (Some vernac_st)
let error loc msg vernac_st = Error ((loc,msg),(Some vernac_st))

type sentence_id = Stateid.t

module SM = Map.Make (Stateid)

type feedback_message = Feedback.level * Loc.t option * Pp.t

type sentence_state =
  | Done of DelegationManager.execution_status
  | Delegated of DelegationManager.job_id * (DelegationManager.execution_status -> unit) option

type delegation_mode =
  | CheckProofsInMaster
  | SkipProofs
  | DelegateProofsToWorkers of { number_of_workers : int }

type options = {
  delegation_mode : delegation_mode;
}
let default_options = { delegation_mode = CheckProofsInMaster }

type state = {
  initial : Vernacstate.t;
  of_sentence : (sentence_state * feedback_message list) SM.t;
}

let init vernac_state = {
  initial = vernac_state;
  of_sentence = SM.empty;
}

let options = ref default_options

let set_options o = options := o
let set_default_options () = options := default_options

type prepared_task =
  | PSkip of sentence_id
  | PExec of executable_sentence
  | PQuery of executable_sentence
  | PDelegate of { terminator_id: sentence_id;
                   opener_id: sentence_id;
                   proof_using: Vernacexpr.section_subset_expr;
                   last_step_id: sentence_id;
                   tasks: prepared_task list;
                 }

module ProofJob = struct
  type update_request =
    | UpdateExecStatus of sentence_id * execution_status
    | AppendFeedback of sentence_id * (Feedback.level * Loc.t option * Pp.t)
  let appendFeedback id fb = AppendFeedback(id,fb)

  type t = {
    tasks : prepared_task list;
    initial_vernac_state : Vernacstate.t;
    doc_id : int;
    terminator_id : sentence_id;
    last_proof_step_id : sentence_id;
  }
  let name = "proof"
  let binary_name = "vscoqtop_proof_worker.opt"
  let initial_pool_size = 1

end

module ProofWorker = DelegationManager.MakeWorker(ProofJob)

type event =
  | LocalFeedback of sentence_id * (Feedback.level * Loc.t option * Pp.t)
  | ProofWorkerEvent of ProofWorker.delegation
type events = event Sel.event list
let pr_event = function
  | LocalFeedback _ -> Pp.str "LocalFeedback"
  | ProofWorkerEvent event -> ProofWorker.pr_event event

let inject_proof_event = Sel.map (fun x -> ProofWorkerEvent x)
let inject_proof_events st l =
  (st, List.map inject_proof_event l)

let interp_error_recovery strategy st : Vernacstate.t =
  match strategy with
  | RSkip -> st
  | RAdmitted ->
    let f = Declare.Proof.save_admitted in
    let open Vernacstate in (* shadows Declare *)
    let open Vernacexpr in
    let open Vernacextend in
    let { Interp.lemmas; program; _ } = st.interp in
    match lemmas with
    | None -> (* if Lemma failed *)
        st
    | Some lemmas ->
        let proof = Vernacstate.LemmaStack.get_top lemmas in
        let pm = NeList.head program in
        let pm = f ~pm ~proof in
        let lemmas = snd (Vernacstate.LemmaStack.pop lemmas) in
        let program = NeList.map_head (fun _ -> pm) program in
        Vernacstate.Declare.set (lemmas,program) [@ocaml.warning "-3"];
        let interp = Vernacstate.Interp.freeze_interp_state ~marshallable:false in
        { st with interp }

(* just a wrapper around vernac interp *)
let interp_ast ~doc_id ~state_id ~st ~error_recovery ast =
    Feedback.set_id_for_feedback doc_id state_id;
    ParTactic.set_id_for_feedback state_id;
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let result =
      try Ok(Vernacinterp.interp_entry ~st ast,[])
      with e when CErrors.noncritical e ->
        let e, info = Exninfo.capture e in
        Error (e, info) in
    Sys.(set_signal sigint Signal_ignore);
    match result with
    | Ok (interp, events) ->
      (*
        log @@ "Executed: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
          " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
          *)
        let st = { st with interp } in
        st, success st, (*List.map inject_pm_event*) events
    | Error (Sys.Break, _ as exn) ->
      (*
        log @@ "Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        *)
        Exninfo.iraise exn
    | Error (e, info) ->
      (*
        log @@ "Failed to execute: " ^ Stateid.to_string state_id ^ "  " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        *)
        let loc = Loc.get_loc info in
        let msg = CErrors.iprint (e, info) in
        let status = error loc (Pp.string_of_ppcmds msg) st in
        let st = interp_error_recovery error_recovery st in
        st, status, []

(* This adapts the Future API with our event model *)
let interp_qed_delayed ~proof_using ~state_id ~st =
  let f proof =
    let proof =
      let env = Global.env () in
      let sigma, _ = Declare.Proof.get_current_context proof in
      let initial_goals pf = Proofview.initial_goals Proof.((data pf).entry) in
      let terms = List.map (fun (_,_,x) -> x) (initial_goals (Declare.Proof.get proof)) in
      let using = Proof_using.definition_using env sigma ~using:proof_using ~terms in
      let vars = Environ.named_context env in
      Names.Id.Set.iter (fun id ->
          if not (List.exists Util.(Context.Named.Declaration.get_id %> Names.Id.equal id) vars) then
            CErrors.user_err
              Pp.(str "Unknown variable: " ++ Names.Id.print id ++ str "."))
        using;
      let _, pstate = Declare.Proof.set_used_variables proof ~using in
      pstate in
    let fix_exn = None in (* FIXME *)
    let f, assign = Future.create_delegate ~blocking:false ~name:"XX" fix_exn in
    Declare.Proof.close_future_proof ~feedback_id:state_id proof f, assign
  in
  let lemmas = Option.get @@ st.Vernacstate.interp.lemmas in
  let proof, assign = Vernacstate.LemmaStack.with_top lemmas ~f in
  let control = [] (* FIXME *) in
  let opaque = Vernacexpr.Opaque in
  let pending = CAst.make @@ Vernacexpr.Proved (opaque, None) in
  (*log "calling interp_qed_delayed done";*)
  let interp = Vernacinterp.interp_qed_delayed_proof ~proof ~st ~control pending in
  (*log "interp_qed_delayed done";*)
  let st = { st with interp } in
  st, success st, assign

let update_all id v fl state =
  { state with of_sentence = SM.add id (v, fl) state.of_sentence }
;;
let update state id v =
  let fl = try snd (SM.find id state.of_sentence) with Not_found -> [] in
  update_all id (Done v) fl state
;;

let local_feedback = Sel.map (fun (x,y) -> LocalFeedback(x,y)) DelegationManager.local_feedback

let handle_feedback id fb state =
  match fb with
  | (Feedback.Info, _, _) -> state
  | (_, _, msg) ->
    begin match SM.find id state.of_sentence with
    | (s,fl) -> update_all id s (fb::fl) state
    | exception Not_found -> 
        log @@ "Received feedback on non-existing state id " ^ Stateid.to_string id ^ ": " ^ Pp.string_of_ppcmds msg;
        state
    end

let handle_event event state =
  match event with
  | LocalFeedback (id,fb) ->
      Some (handle_feedback id fb state), []
  | ProofWorkerEvent event ->
      let update, events = ProofWorker.handle_event event in
      let state =
        match update with
        | None -> None
        | Some (ProofJob.AppendFeedback(id,fb)) ->
            Some (handle_feedback id fb state)
        | Some (ProofJob.UpdateExecStatus(id,v)) ->
            match SM.find id state.of_sentence with
            | (Delegated (_,completion), fl) ->
                Option.default ignore completion v;
                Some (update_all id (Done v) fl state)
            | (Done _, fl) -> None (* TODO: is this possible? *)
            | exception Not_found -> None (* TODO: is this possible? *)
      in
      inject_proof_events state events

let find_fulfilled_opt x m =
  try
    let ss,_ = SM.find x m in
    match ss with
    | Done x -> Some x
    | Delegated _ -> None
  with Not_found -> None

let jobs : (DelegationManager.job_id * Sel.cancellation_handle * ProofJob.t) Queue.t = Queue.create ()

let rec prepare_task task : prepared_task list =
  match task with
  | Skip id -> [PSkip id]
  | Exec e -> [PExec e]
  | Query e -> [PQuery e]
  | OpaqueProof { terminator; opener_id; tasks; proof_using} ->
      match !options.delegation_mode with
      | DelegateProofsToWorkers _ ->
          log "delegating proofs to workers";
          let last_step_id = (CList.last tasks).id in
          let tasks = List.map (fun x -> PExec x) tasks in
          [PDelegate {terminator_id = terminator.id; opener_id; last_step_id; tasks; proof_using}]
      | CheckProofsInMaster ->
          log "running the proof in master as per config";
          List.map (fun x -> PExec x) tasks @ [PExec terminator]
      | SkipProofs ->
          log (Printf.sprintf "skipping proof made of %d tasks" (List.length tasks));
          let tasks = [] in
          let last_step_id = (CList.last tasks).id in
          [PDelegate {terminator_id = terminator.id; opener_id; last_step_id; tasks; proof_using}]

let id_of_prepared_task = function
  | PSkip id -> id
  | PExec ex -> ex.id
  | PQuery ex -> ex.id
  | PDelegate { terminator_id } -> terminator_id

let purge_state = function
  | Success _ -> Success None
  | Error(e,_) -> Error (e,None)

let ensure_proof_over = function
  | Success (Some st) as x ->
     (* uncomment to see the size of state/proof.
      log @@ Printf.sprintf "final state: %d\n" (Bytes.length @@ Marshal.to_bytes x []);
      let f proof = log @@ Printf.sprintf "final proof: %d\n" (Bytes.length @@ Marshal.to_bytes (Declare.Proof.return_proof proof) []) in
      Vernacstate.LemmaStack.with_top (Option.get @@ st.Vernacstate.lemmas) ~f; *)
     Vernacstate.LemmaStack.with_top (Option.get @@ st.Vernacstate.interp.lemmas)
       ~f:(fun p -> if Proof.is_done @@ Declare.Proof.get p then x else Error((None,"Proof is not finished"),None))
  | x -> x

(* TODO move to proper place *)
let worker_execute ~doc_id last_step_id ~send_back (vs,events) = function
  | PSkip id ->
    (vs, events)
  | PExec { id; ast; synterp; error_recovery } ->
    let vs = { vs with Vernacstate.synterp } in
    log ("worker interp " ^ Stateid.to_string id);
    let vs, v, ev = interp_ast ~doc_id ~state_id:id ~st:vs ~error_recovery ast in
    let v = if Stateid.equal id last_step_id then ensure_proof_over v else v in
    send_back (ProofJob.UpdateExecStatus (id,purge_state v));
    (vs, events @ ev)
  | _ -> assert false

let worker_main { ProofJob.tasks; initial_vernac_state = vs; doc_id; last_proof_step_id; _ } ~send_back =
  try
    let _ = List.fold_left (worker_execute ~doc_id last_proof_step_id ~send_back) (vs,[]) tasks in
    flush_all ();
    exit 0
  with e ->
    let e, info = Exninfo.capture e in
    let message = CErrors.iprint_no_report (e, info) in
    Feedback.msg_debug @@ Pp.str "======================= worker ===========================";
    Feedback.msg_debug message;
    Feedback.msg_debug @@ Pp.str "==========================================================";
    exit 1

let execute ~doc_id st (vs, events, interrupted) task =
  if interrupted then begin
    let st = update st (id_of_prepared_task task) (Error ((None,"interrupted"),None)) in
    (st, vs, events, true)
  end else
    try
      match task with
      | PSkip id ->
          let st = update st id (success vs) in
          (st, vs, events, false)
      | PExec { id; ast; synterp; error_recovery } ->
          let vs = { vs with Vernacstate.synterp } in
          let vs, v, ev = interp_ast ~doc_id ~state_id:id ~st:vs ~error_recovery ast in
          let st = update st id v in
          (st, vs, events @ ev, false)
      | PQuery { id; ast; synterp; error_recovery } ->
          let vs = { vs with Vernacstate.synterp } in
          let _, v, ev = interp_ast ~doc_id ~state_id:id ~st:vs ~error_recovery ast in
          let st = update st id v in
          (st, vs, events @ ev, false)
      | PDelegate { terminator_id; opener_id; last_step_id; tasks; proof_using } ->
          begin match find_fulfilled_opt opener_id st.of_sentence with
          | Some (Success _) ->
            let job =  { ProofJob.tasks; initial_vernac_state = vs; doc_id; terminator_id; last_proof_step_id  = last_step_id } in
            let job_id = DelegationManager.mk_job_id terminator_id in
            (* The proof was successfully opened *)
            let last_vs, v, assign = interp_qed_delayed ~state_id:terminator_id ~proof_using ~st:vs in
            let complete_job status =
              try match status with
              | Success None ->
                log "Resolved future (without sending back the witness)";
                assign (`Exn (Failure "no proof",Exninfo.null))
              | Success (Some vernac_st) ->
                let f proof =
                  log "Resolved future";
                  assign (`Val (Declare.Proof.return_proof proof))
                in
                Vernacstate.LemmaStack.with_top (Option.get @@ vernac_st.Vernacstate.interp.lemmas) ~f
              | Error ((loc,err),_) ->
                  log "Aborted future";
                  assign (`Exn (CErrors.UserError(Pp.str err), Option.fold_left Loc.add_loc Exninfo.null loc))
              with exn when CErrors.noncritical exn ->
                assign (`Exn (CErrors.UserError(Pp.str "error closing proof"), Exninfo.null))
            in
            let st = update st terminator_id (success last_vs) in
            let st = List.fold_left (fun st id ->
               if Stateid.equal id last_step_id then
                 update_all id (Delegated (job_id,Some complete_job)) [] st
               else
                 update_all id (Delegated (job_id,None)) [] st)
               st (List.map id_of_prepared_task tasks) in
            if tasks = [] then (st, last_vs, events, false)
            else begin
              let e, cancellation =
                ProofWorker.worker_available ~jobs
                  ~fork_action:worker_main in
              Queue.push (job_id, cancellation, job) jobs;
              (st, last_vs,events @ [inject_proof_event e] ,false)
            end
          | _ ->
            (* If executing the proof opener failed, we skip the proof *)
            let st = update st terminator_id (success vs) in
            (st, vs,events,false)
          end
    with Sys.Break ->
      let st = update st (id_of_prepared_task task) (Error ((None,"interrupted"),None)) in
      (st, vs, events, true)

let build_tasks_for sch st id =
  let rec build_tasks id tasks =
    begin match find_fulfilled_opt id st.of_sentence with
    | Some (Success (Some vs)) ->
      (* We reached an already computed state *)
      log @@ "Reached computed state " ^ Stateid.to_string id;
      vs, tasks
    | Some (Error(_,Some vs)) ->
      (* We try to be resilient to an error *)
      log @@ "Error resiliency on state " ^ Stateid.to_string id;
      vs, tasks
    | _ ->
      log @@ "Non (locally) computed state " ^ Stateid.to_string id;
      let (base_id, task) = task_for_sentence sch id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        st.initial, task :: tasks
      | Some base_id ->
        build_tasks base_id (task::tasks)
      end
    end
  in
  let vs, tasks = build_tasks id [] in
  vs, List.concat_map prepare_task tasks

let errors st =
  List.fold_left (fun acc (id, (p,_)) ->
    match p with
    | Done (Error ((loc,e),_st)) -> (id,(loc,e)) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.of_sentence

let mk_feedback id (lvl,loc,msg) = (id,(lvl,loc,Pp.string_of_ppcmds msg))

let feedback st =
  List.fold_left (fun acc (id, (_,l)) -> List.map (mk_feedback id) l @ acc) [] @@ SM.bindings st.of_sentence

let shift_locs st pos offset =
  (* FIXME shift loc in feedback *)
  let shift_error (p,r as orig) = match p with
  | Done (Error ((Some loc,e),st)) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then ((Done (Error ((Some (Loc.shift_loc offset offset loc),e),st))),r)
    else if stop >= pos then ((Done (Error ((Some (Loc.shift_loc 0 offset loc),e),st))),r)
    else orig
  | _ -> orig
  in
  { st with of_sentence = SM.map shift_error st.of_sentence }

let executed_ids st =
  SM.fold (fun id (p,_) acc ->
    match p with
    | Done _ -> id :: acc
    | _ -> acc) st.of_sentence []

let is_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success (Some _) | Error (_,Some _)) -> true
  | _ -> false

let is_remotely_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success None | Error (_,None)) -> true
  | _ -> false

let invalidate1 of_sentence id =
  try
    let p,_ = SM.find id of_sentence in
    match p with
    | Delegated (job_id,_) ->
        DelegationManager.cancel_job job_id;
        SM.remove id of_sentence
    | _ -> SM.remove id of_sentence
  with Not_found -> of_sentence

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let of_sentence = invalidate1 st.of_sentence id in
  let old_jobs = Queue.copy jobs in
  let removed = ref [] in
  Queue.clear jobs;
  Queue.iter (fun ((_, cancellation, { ProofJob.terminator_id; tasks }) as job) ->
    if terminator_id != id then
      Queue.push job jobs
    else begin
      Sel.cancel cancellation;
      removed := tasks :: !removed
    end) old_jobs;
  let of_sentence = List.fold_left invalidate1 of_sentence
    List.(concat (map (fun tasks -> map id_of_prepared_task tasks) !removed)) in
  if of_sentence == st.of_sentence then st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (invalidate schedule) deps { st with of_sentence }

let get_proof st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log "Cannot find state for proof"; None
  | Some (Error _) -> log "Proof requested in error state"; None
  | Some (Success None) -> log "Proof requested in a remotely checked state"; None
  | Some (Success (Some { interp = { Vernacstate.Interp.lemmas = None; _ } })) -> log "Proof requested in a state with no proof"; None
  | Some (Success (Some { interp = { Vernacstate.Interp.lemmas = Some st; _ } })) ->
      log "Proof is there";
      let open Proof in
      let open Declare in
      let open Vernacstate in
      st |> LemmaStack.with_top ~f:Proof.get |> Option.make

let get_proofview st id = Option.map Proof.data (get_proof st id)

let get_lemmas sigma env =
  let open CompletionItems in
  let results = ref [] in
  let display ref kind env c =
    results := mk_completion_item sigma ref kind env c :: results.contents;
  in
  Search.generic_search env display;
  results.contents

let get_context st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log "Cannot find state for get_context"; None
  | Some (Error _) -> log "Context requested in error state"; None
  | Some (Success None) -> log "Context requested in a remotely checked state"; None
  | Some (Success (Some { interp = { Vernacstate.Interp.lemmas = Some st; _ } })) ->
    let open Proof in
    let open Declare in
    let open Vernacstate in
    st |> LemmaStack.with_top ~f:Proof.get_current_context |> Option.make
  | Some (Success (Some { interp = st })) ->
    Vernacstate.Interp.unfreeze_interp_state st;
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Some (sigma, env)

module ProofWorkerProcess = struct
  type options = ProofWorker.options
  let parse_options = ProofWorker.parse_options
  let main ~st:_ options =
    let send_back, job = ProofWorker.setup_plumbing options in
    worker_main job ~send_back
  let log = ProofWorker.log
end

