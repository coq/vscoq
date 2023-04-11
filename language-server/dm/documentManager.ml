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
open Lsp.LspData

let Log log = Log.mk_log "documentManager"

type proof_data = (Proof.data * Position.t) option

module SM = Map.Make (Stateid)

type encompassing_range = {
  ids : Range.t SM.t;
  start : Position.t;
  end_ : Position.t;
}

let empty_encompassing_range = {
  ids = SM.empty;
  start = { line = 0; character = 0 };
  end_ = { line = 0; character = 0 };
}

  
type state = {
  uri : string;
  init_vs : Vernacstate.t;
  opts : Coqargs.injection_command list;
  document : Document.document;
  execution_state : ExecutionManager.state;
  observe_id : Types.sentence_id option; (* TODO materialize observed loc and line-by-line execution status *)
  checked : encompassing_range list;
}

let add_sentence doc id (range : encompassing_range) = 
  let sentence_range = Document.range_of_exec_id doc id in
  let ids = SM.add id sentence_range range.ids in
  if SM.cardinal ids = 1 then
    { ids; start = sentence_range.start; end_ = sentence_range.end_ }
  else
    let start = if sentence_range.start < range.start then sentence_range.start else range.start in
    let end_ = if sentence_range.end_ > range.end_ then sentence_range.end_ else range.end_ in
    { ids; start; end_ }

let merge_ranges a b = 
  let ids = SM.add_seq (SM.to_seq b.ids) a.ids in
  let start = min a.start b.start in
  let end_ = max a.end_ b.end_ in
  {ids; start; end_}

let sentence_checked st id =  let sentence_range = Document.range_of_exec_id st.document id in
  let start, end_ = (sentence_range.start, sentence_range.end_) in
  let only_new = add_sentence st.document id empty_encompassing_range in
  let rec aux f (ranges : encompassing_range list) = match ranges with 
    | x :: xs when f x -> merge_ranges x only_new :: xs
    | x :: xs when x.end_ < end_ -> x :: only_new :: xs (* We did not find a good merge before going past the end *)
    | x :: xs -> x :: aux f xs
    | [] -> [only_new]
  in
  match Document.surrounding_sentences st.document id with
  | None, None -> aux (fun _ -> false) st.checked
  | Some before, None -> aux (fun x -> SM.mem before.id x.ids) st.checked
  | None, Some after -> aux (fun x -> SM.mem after.id x.ids) st.checked
  | Some before, Some after -> 
  let rec aux (ranges : encompassing_range list) = match ranges with 
    | x :: y :: xs when (SM.mem before.id x.ids && SM.mem after.id y.ids) -> 
      (merge_ranges x only_new |> merge_ranges y) :: xs
    | x :: xs when (SM.mem before.id x.ids || SM.mem after.id x.ids) -> merge_ranges x only_new :: xs
    | x :: xs when x.end_ < end_ -> x :: only_new :: xs (* We did not find a good merge before going past the end *)
    | x :: xs -> x :: aux xs
    | [] -> [only_new]
  in
  aux st.checked

(* Document.surrounding_sentences st.document id 
Need to check the surronding sentences and probably have more ranges which can also be merged later.   

*)

type event =
  | Execute of { (* we split the computation to help interruptibility *)
      id : Types.sentence_id; (* sentence of interest *)
      vst_for_next_todo : Vernacstate.t; (* the state to be used for the next
        todo, it is not necessarily the state of the last sentence, since it
        may have failed and this is a surrogate used for error resiliancy *)
      todo : ExecutionManager.prepared_task list;
      started : float; (* time *)
    }
  | ExecutionManagerEvent of ExecutionManager.event
let pp_event fmt = function
  | Execute { id; todo; started; _ } ->
      let time = Unix.gettimeofday () -. started in 
      Stdlib.Format.fprintf fmt "ExecuteToLoc %d (%d tasks left, started %2.3f ago)" (Stateid.to_int id) (List.length todo) time
  | ExecutionManagerEvent _ -> Stdlib.Format.fprintf fmt "ExecutionManagerEvent"

let inject_em_event x = Sel.map (fun e -> ExecutionManagerEvent e) x
let inject_em_events events = List.map inject_em_event events

type events = event Sel.event list

type exec_overview = {
  parsed : Range.t list;
  checked : Range.t list;
  legacy_highlight : Range.t list;
}

let is_executed execution_state id = 
  ExecutionManager.is_executed execution_state id || ExecutionManager.is_remotely_executed execution_state id

let executed_ranges doc execution_state loc =
  let ranges_of l =
    List.sort (fun { Range.start = s1 } { Range.start = s2 } -> compare s1 s2) @@
    List.map (Document.range_of_exec_id doc) l in
  let ids = List.map (fun s -> s.Document.id) @@ Document.sentences doc in
  let executed_ids = List.filter (ExecutionManager.is_executed execution_state) ids in
  let parsed_ids = List.filter (fun x -> not (is_executed execution_state x)) ids in
  let legacy_ids = List.filter (is_executed execution_state) ids in
  { 
    parsed = ranges_of parsed_ids;
    checked = ranges_of executed_ids;
    legacy_highlight = ranges_of legacy_ids; 
  }

let executed_ranges (st : state) =
  let checked = List.map (fun x -> { Range.start = x.start; Range.end_ = x.end_ }) st.checked in
  { 
    parsed = [];
    checked = [];
    legacy_highlight = checked; 
  }

let make_diagnostic doc id oloc message severity =
  let range =
    match oloc with
    | None -> Document.range_of_exec_id doc id
    | Some loc ->
      Document.range_of_coq_loc doc loc
  in
  Diagnostic.{ range; message; severity }

let diagnostics st =
  let parse_errors = Document.parse_errors st.document in
  let all_exec_errors = ExecutionManager.errors st.execution_state in
  let all_feedback = ExecutionManager.feedback st.execution_state in
  (* we are resilient to a state where invalidate was not called yet *)
  let exists (id,_) = Option.has_some (Document.get_sentence st.document id) in
  let exec_errors = all_exec_errors |> List.filter exists in
  let feedback = all_feedback |> List.filter exists in
  let mk_diag (id,(lvl,oloc,msg)) =
    make_diagnostic st.document id oloc msg lvl
  in
  let mk_error_diag (id,(oloc,msg)) = mk_diag (id,(Feedback.Error,oloc,msg)) in
  List.map mk_error_diag parse_errors @
    List.map mk_error_diag exec_errors @
    List.map mk_diag feedback

let init init_vs ~opts ~uri ~text =
  let document = Document.create_document text in
  Vernacstate.unfreeze_full_state init_vs;
  let top = Coqargs.(dirpath_of_top (TopPhysical uri)) in
  Coqinit.start_library ~top opts;
  let execution_state = ExecutionManager.init (Vernacstate.freeze_full_state ~marshallable:false) in
  { uri; opts; init_vs; document; execution_state; observe_id = None; checked = [] }, [inject_em_event ExecutionManager.local_feedback]

let reset { uri; opts; init_vs; document } =
  let document = Document.create_document (Document.text document) in
  Vernacstate.unfreeze_full_state init_vs;
  let top = Coqargs.(dirpath_of_top (TopPhysical uri)) in
  Coqinit.start_library ~top opts;
  let execution_state = ExecutionManager.init (Vernacstate.freeze_full_state ~marshallable:false) in
  { uri; opts; init_vs; document; execution_state; observe_id = None; checked = []}

let interpret_to_loc state loc : (state * event Sel.event list) =
    let invalid_ids, document = Document.validate_document state.document in
    let execution_state =
      List.fold_left (fun st id ->
        ExecutionManager.invalidate (Document.schedule state.document) id st
        ) state.execution_state (Stateid.Set.elements invalid_ids) in
    let state = { state with document; execution_state } in
    (* We jump to the sentence before the position, otherwise jumping to the
    whitespace at the beginning of a sentence will observe the state after
    executing the sentence, which is unnatural. *)
    match Document.find_sentence_before state.document loc with
    | None -> (* document is empty *) (state, [])
    | Some { id; stop; start } ->
      let state = { state with observe_id = Some id } in
      let vst_for_next_todo, todo = ExecutionManager.build_tasks_for state.document state.execution_state id in
      if CList.is_empty todo then
        (state, [])
      else
        (state, [Sel.now (Execute {id; vst_for_next_todo; todo; started = Unix.gettimeofday () })])

let interpret_to state id : (state * event Sel.event list) =
  let invalid_ids, document = Document.validate_document state.document in
  let execution_state =
    List.fold_left (fun st id ->
      ExecutionManager.invalidate (Document.schedule state.document) id st
      ) state.execution_state (Stateid.Set.elements invalid_ids) in
  let state = { state with document; execution_state } in
  (* We jump to the sentence before the position, otherwise jumping to the
  whitespace at the beginning of a sentence will observe the state after
  executing the sentence, which is unnatural. *)
  match Document.get_sentence state.document id with
  | None -> (state, []) (* TODO error? *)
  | Some { id; stop; start } ->
    let state = { state with observe_id = Some id } in
    let vst_for_next_todo, todo = ExecutionManager.build_tasks_for state.document state.execution_state id in
    if CList.is_empty todo then
      (state, [])
    else
      (state, [Sel.now (Execute {id; vst_for_next_todo; todo; started = Unix.gettimeofday () })])

let interpret_to_position st pos =
  let loc = Document.position_to_loc st.document pos in
  match Document.find_sentence_before st.document loc with
  | None -> (st, []) (* document is empty *)
  | Some { id } -> interpret_to st id

let interpret_to_previous st =
  match st.observe_id with
  | None -> (st, [])
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> (st, []) (* TODO error? *)
    | Some { id; stop; start} ->
      match Document.find_sentence_before st.document start with
      | None -> (st, [])
      | Some {id } -> interpret_to st id

let interpret_to_next st =
  match st.observe_id with
  | None -> 
    begin match Document.find_sentence st.document 0 with
    | None -> (st, []) (*The document is empty*)
    | Some {id} -> interpret_to st id
    end
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> (st, []) (* TODO error? *)
    | Some { id; stop; start} ->
      match Document.find_sentence_after st.document (stop+1) with
      | None -> (st, [])
      | Some {id } -> interpret_to st id

let interpret_to_end st =
  match Document.get_last_sentence st.document with 
  | None -> (st, [])
  | Some {id} -> interpret_to st id

let retract state loc =
  match Option.bind state.observe_id (Document.get_sentence state.document) with
  | None -> state
  | Some { start } ->
    if loc < start then
      let observe_id = Option.map (fun s -> s.Document.id) @@ Document.find_sentence_before state.document loc in
      { state with observe_id }
    else state

let apply_text_edits state edits =
  let document = Document.apply_text_edits state.document edits in
  let state = { state with document } in
  retract state (Document.parsed_loc document) 

let validate_document state =
  let invalid_ids, document = Document.validate_document state.document in
  let execution_state =
    List.fold_left (fun st id ->
      ExecutionManager.invalidate (Document.schedule state.document) id st
      ) state.execution_state (Stateid.Set.elements invalid_ids) in
  { state with document; execution_state }

let handle_event ev st =
  match ev with
  | Execute { id; todo = []; started } -> (* the vst_for_next_todo is also in st.execution_state *)
    let time = Unix.gettimeofday () -. started in 
    log (Printf.sprintf "ExecuteToLoc %d ends after %2.3f" (Stateid.to_int id) time);
    (* We update the state to trigger a publication of diagnostics *)
    (Some st, [])
  | Execute { id; vst_for_next_todo; started; todo = task :: todo } ->
    (*log "Execute (more tasks)";*)
    let doc_id = Document.id_of_doc st.document in
    let (execution_state,vst_for_next_todo,events,interrupted, executed_id) =
      ExecutionManager.execute ~doc_id st.execution_state (vst_for_next_todo, [], false) task in
    (* We do not update the state here because we may have received feedback while
       executing *)
    (
    match executed_id with 
    | None -> (Some {st with execution_state}, inject_em_events events @ [Sel.now (Execute {id; vst_for_next_todo; todo; started })])
    | Some id ->
      let checked = sentence_checked st id in
      let st = {st with execution_state; checked} in
      (Some st, inject_em_events events @ [Sel.now (Execute {id; vst_for_next_todo; todo; started })])
    )
  | ExecutionManagerEvent ev ->
    let execution_state_update, events = ExecutionManager.handle_event ev st.execution_state in
    (Option.map (fun execution_state -> {st with execution_state}) execution_state_update, inject_em_events events)

let get_proof st pos =
  let id_of_pos pos =
    let loc = Document.position_to_loc st.document pos in
    match Document.find_sentence_before st.document loc with
    | None -> None
    | Some { id } -> Some id
  in
  let oid = Option.cata id_of_pos st.observe_id pos in
  Option.bind oid (ExecutionManager.get_proofview st.execution_state)

let get_context st pos =
  let loc = Document.position_to_loc st.document pos in
  match Document.find_sentence_before st.document loc with
  | None -> None
  | Some sentence ->
    ExecutionManager.get_context st.execution_state sentence.id

let get_lemmas st pos =
  match get_context st pos with
  | None -> None
  | Some (sigma, env) -> 
    Some (ExecutionManager.get_lemmas sigma env)

let parse_entry st pos entry pattern =
  let pa = Pcoq.Parsable.make (Gramlib.Stream.of_string pattern) in
  let loc = Document.position_to_loc st.document pos in
  let st = match Document.find_sentence_before st.document loc with
  | None -> st.init_vs.Vernacstate.synterp.parsing
  | Some { synterp_state } -> synterp_state.Vernacstate.Synterp.parsing
  in
  Vernacstate.Parser.parse st entry pa

let about st pos ~goal ~pattern =
  match get_context st pos with 
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma, env) ->
    try
      let ref_or_by_not = parse_entry st pos (Pcoq.Prim.smart_global) pattern in
      let udecl = None (* TODO? *) in
      Ok (Pp.string_of_ppcmds @@ Prettyp.print_about env sigma ref_or_by_not udecl)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

let search st ~id pos pattern =
  match get_context st pos with
  | None -> [] (* TODO execute? *)
  | Some (sigma, env) ->
    let query = parse_entry st pos (G_vernac.search_query) pattern in
    SearchQuery.interp_search ~id env sigma query

let hover st pos = 
  let opattern = Document.word_at_position st.document pos in
  Option.map (fun pattern -> about st pos ~goal:None ~pattern) opattern

let check st pos ~goal ~pattern =
  match get_context st pos with 
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma,env) ->
    let rc = parse_entry st pos Pcoq.Constr.lconstr pattern in
    try
      let redexpr = None in
      Ok (Pp.string_of_ppcmds @@ Vernacentries.check_may_eval env sigma redexpr rc)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

let locate st pos ~pattern = 
  match parse_entry st pos (Pcoq.Prim.smart_global) pattern with
  | { v = AN qid } -> Ok (Pp.string_of_ppcmds @@ Prettyp.print_located_qualid qid)
  | { v = ByNotation (ntn, sc)} -> 
    match get_context st pos with
    | None -> Error("No context found")
    | Some (sigma, env) -> 
      Ok( Pp.string_of_ppcmds @@ Notation.locate_notation
        (Constrextern.without_symbols (Printer.pr_glob_constr_env env sigma)) ntn sc)

let print st pos ~pattern = 
  match get_context st pos with 
  | None -> Error("No context found")
  | Some (sigma, env) -> 
    let qid = parse_entry st pos (Pcoq.Prim.smart_global) pattern in
    let udecl = None in (*TODO*)
    Ok ( Pp.string_of_ppcmds @@ Prettyp.print_name env sigma qid udecl )

module Internal = struct

  let document st =
    st.document

end
