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

type state = {
  uri : Uri.t;
  init_vs : Vernacstate.t;
  opts : Coqargs.injection_command list;
  document : Document.document;
  execution_state : ExecutionManager.state;
  observe_id : Types.sentence_id option; (* TODO materialize observed loc and line-by-line execution status *)
}

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
  checked_by_delegate : Range.t list;
  legacy_highlight : Range.t list;
}

let merge_ranges doc (r1,l) r2 =
  let loc1 = RawDocument.loc_of_position doc r1.Range.end_ in
  let loc2 = RawDocument.loc_of_position doc r2.Range.start in
  if RawDocument.only_whitespace_between doc (loc1+1) (loc2-1) then
    Range.{ start = r1.Range.start; end_ = r2.Range.end_ }, l
  else
    r2, r1 :: l

let compress_ranges doc = function
  | [] -> []
  | range :: tl ->
    let r, l = List.fold_left (merge_ranges doc) (range,[]) tl in
    r :: l

let executed_ranges doc execution_state loc =
  let ranges_of l =
    compress_ranges (Document.raw_document doc) @@
    List.sort (fun { Range.start = s1 } { Range.start = s2 } -> compare s1 s2) @@
    List.map (Document.range_of_id doc) l in
  let ids_before_loc = List.map (fun s -> s.Document.id) @@ Document.sentences_before doc loc in
  let ids = List.map (fun s -> s.Document.id) @@ Document.sentences doc in
  let executed_ids = List.filter (ExecutionManager.is_executed execution_state) ids in
  let remotely_executed_ids = List.filter (ExecutionManager.is_remotely_executed execution_state) ids in
  let parsed_ids = List.filter (fun x -> not (List.mem x executed_ids || List.mem x remotely_executed_ids)) ids in
  let legacy_ids = List.filter (fun x -> ExecutionManager.is_executed execution_state x || ExecutionManager.is_remotely_executed execution_state x) ids_before_loc in
  log @@ Printf.sprintf "highlight: legacy: %s" (String.concat " " (List.map Stateid.to_string legacy_ids));
  log @@ Printf.sprintf "highlight: parsed: %s" (String.concat " " (List.map Stateid.to_string parsed_ids));
  log @@ Printf.sprintf "highlight: parsed + checked: %s" (String.concat " " (List.map Stateid.to_string executed_ids));
  log @@ Printf.sprintf "highlight: parsed + checked_by_delegate: %s" (String.concat " " (List.map Stateid.to_string remotely_executed_ids));
  { 
    parsed = ranges_of parsed_ids;
    checked = ranges_of executed_ids;
    checked_by_delegate = ranges_of remotely_executed_ids;
    legacy_highlight = ranges_of legacy_ids; 
  }

let executed_ranges st =
  match Option.bind st.observe_id (Document.get_sentence st.document) with
  | None ->
    let end_loc = RawDocument.end_loc @@ Document.raw_document st.document in
    executed_ranges st.document st.execution_state end_loc
  | Some { stop } -> executed_ranges st.document st.execution_state stop

let make_diagnostic doc range oloc message severity =
  let range =
    match oloc with
    | None -> range
    | Some loc ->
      RawDocument.range_of_loc (Document.raw_document doc) loc
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
    make_diagnostic st.document (Document.range_of_id st.document id) oloc msg lvl
  in
  let mk_error_diag (id,(oloc,msg)) = mk_diag (id,(Feedback.Error,oloc,msg)) in
  let mk_parsing_error_diag Document.{ msg = (oloc,msg); start; stop } =
    let doc = Document.raw_document st.document in
    let severity = Feedback.Error in
    let start = RawDocument.position_of_loc doc start in
    let end_ = RawDocument.position_of_loc doc stop in
    let range = Range.{ start; end_ } in
    make_diagnostic st.document range oloc msg severity
  in
  List.map mk_parsing_error_diag parse_errors @
    List.map mk_error_diag exec_errors @
    List.map mk_diag feedback

let init init_vs ~opts uri ~text =
  let document = Document.create_document text in
  Vernacstate.unfreeze_full_state init_vs;
  let top = Coqargs.(dirpath_of_top (TopPhysical (Uri.path uri))) in
  Coqinit.start_library ~top opts;
  let execution_state, feedback = ExecutionManager.init (Vernacstate.freeze_full_state ~marshallable:false) in
  { uri; opts; init_vs; document; execution_state; observe_id = None }, [inject_em_event feedback]

let reset { uri; opts; init_vs; document; execution_state } =
  let text = RawDocument.text @@ Document.raw_document document in
  let document = Document.create_document text in
  Vernacstate.unfreeze_full_state init_vs;
  let top = Coqargs.(dirpath_of_top (TopPhysical (Uri.path uri))) in
  Coqinit.start_library ~top opts;
  ExecutionManager.destroy execution_state;
  let execution_state, feedback = ExecutionManager.init (Vernacstate.freeze_full_state ~marshallable:false) in
  { uri; opts; init_vs; document; execution_state; observe_id = None }, [inject_em_event feedback]

let interpret_to state id : (state * event Sel.event list) =
  match Document.get_sentence state.document id with
  | None -> (state, []) (* TODO error? *)
  | Some { id } ->
    let state = { state with observe_id = Some id } in
    let vst_for_next_todo, todo = ExecutionManager.build_tasks_for (Document.schedule state.document) state.execution_state id in
    if CList.is_empty todo then
      (state, [])
    else
      (state, [Sel.now (Execute {id; vst_for_next_todo; todo; started = Unix.gettimeofday () })])

let interpret_to_position st pos =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match Document.find_sentence_before st.document loc with
  | None -> (st, []) (* document is empty *)
  | Some { id } -> interpret_to st id

let interpret_to_previous st =
  match st.observe_id with
  | None -> (st, [])
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> (st, []) (* TODO error? *)
    | Some { start} ->
      match Document.find_sentence_before st.document start with
      | None -> (st, [])
      | Some {id } -> interpret_to st id

let interpret_to_next st =
  match st.observe_id with
  | None -> 
    begin match Document.get_first_sentence st.document with
    | None -> log ("Matched find sentence to none"); (st, []) (*The document is empty*)
    | Some {id} -> log ("Matched oberve_id to " ^ Stateid.to_string id); interpret_to st id
    end
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> (st, []) (* TODO error? *)
    | Some { stop } ->
      match Document.find_sentence_after st.document (stop+1) with
      | None -> (st, [])
      | Some {id } -> interpret_to st id

let interpret_to_end st =
  match Document.get_last_sentence st.document with (* FIXME last sentence should be computed after document validation *)
  | None -> (st, [])
  | Some {id} -> log ("interpret_to_end id = " ^ Stateid.to_string id); interpret_to st id

let retract state loc =
  match Option.bind state.observe_id (Document.get_sentence state.document) with
  | None -> state
  | Some { stop } ->
    if loc < stop then
      let observe_id = Option.map (fun s -> s.Document.id) @@ Document.find_sentence_before state.document loc in
      { state with observe_id }
    else state

let apply_text_edits state edits =
  let document, loc = Document.apply_text_edits state.document edits in
  let state = { state with document } in
  retract state loc

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
    let (execution_state,vst_for_next_todo,events,_interrupted) =
      ExecutionManager.execute st.execution_state (vst_for_next_todo, [], false) task in
    (* We do not update the state here because we may have received feedback while
       executing *)
    (Some {st with execution_state}, inject_em_events events @ [Sel.now (Execute {id; vst_for_next_todo; todo; started })])
  | ExecutionManagerEvent ev ->
    let execution_state_update, events = ExecutionManager.handle_event ev st.execution_state in
    (Option.map (fun execution_state -> {st with execution_state}) execution_state_update, inject_em_events events)

let get_proof st pos =
  let id_of_pos pos =
    let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
    match Document.find_sentence_before st.document loc with
    | None -> None
    | Some { id } -> Some id
  in
  let oid = Option.cata id_of_pos st.observe_id pos in
  Option.bind oid (ExecutionManager.get_proofview st.execution_state)

let get_context st pos =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
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
  let st = match Document.find_sentence_before st.document pos with
  | None -> st.init_vs.Vernacstate.synterp.parsing
  | Some { synterp_state } -> synterp_state.Vernacstate.Synterp.parsing
  in
  Vernacstate.Parser.parse st entry pa

let about st pos ~pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with 
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma, env) ->
    try
      let ref_or_by_not = parse_entry st loc (Pcoq.Prim.smart_global) pattern in
      let udecl = None (* TODO? *) in
      Ok (Pp.string_of_ppcmds @@ Prettyp.print_about env sigma ref_or_by_not udecl)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

let search st ~id pos pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> [] (* TODO execute? *)
  | Some (sigma, env) ->
    let query = parse_entry st loc (G_vernac.search_query) pattern in
    SearchQuery.interp_search ~id env sigma query

let hover st pos = 
  let opattern = RawDocument.word_at_position (Document.raw_document st.document) pos in
  Option.map (fun pattern -> about st pos ~pattern) opattern

let check st pos ~pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with 
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma,env) ->
    let rc = parse_entry st loc Pcoq.Constr.lconstr pattern in
    try
      let redexpr = None in
      Ok (Pp.string_of_ppcmds @@ Vernacentries.check_may_eval env sigma redexpr rc)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

let locate st pos ~pattern = 
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match parse_entry st loc (Pcoq.Prim.smart_global) pattern with
  | { v = AN qid } -> Ok (Pp.string_of_ppcmds @@ Prettyp.print_located_qualid qid)
  | { v = ByNotation (ntn, sc)} -> 
    match get_context st pos with
    | None -> Error("No context found")
    | Some (sigma, env) -> 
      Ok( Pp.string_of_ppcmds @@ Notation.locate_notation
        (Constrextern.without_symbols (Printer.pr_glob_constr_env env sigma)) ntn sc)

let print st pos ~pattern = 
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with 
  | None -> Error("No context found")
  | Some (sigma, env) -> 
    let qid = parse_entry st loc (Pcoq.Prim.smart_global) pattern in
    let udecl = None in (*TODO*)
    Ok ( Pp.string_of_ppcmds @@ Prettyp.print_name env sigma qid udecl )

module Internal = struct

  let document st =
    st.document

  let execution_state st =
    st.execution_state

  let observe_id st =
    st.observe_id

  let string_of_state st =
    let sentences = Document.sentences_sorted_by_loc st.document in
    let string_of_state id =
      if ExecutionManager.is_executed st.execution_state id then "(executed)"
      else if ExecutionManager.is_remotely_executed st.execution_state id then "(executed in worker)"
      else "(not executed)"
    in
    let string_of_sentence sentence =
      Document.Internal.string_of_sentence sentence ^ " " ^ string_of_state sentence.id
    in
    String.concat "\n" @@ List.map string_of_sentence sentences

end
