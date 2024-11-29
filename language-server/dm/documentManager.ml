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

open Lsp.Types
open Protocol
open Protocol.LspWrapper
open Protocol.ExtProtocol
open Protocol.Printing
open Types

let Log log = Log.mk_log "documentManager"

type observe_id = Id of Types.sentence_id | Top

type blocking_error = {
  last_range: Range.t;
  error_range: Range.t
}

let to_sentence_id = function
| Top -> None
| Id id -> Some id

type state = {
  uri : DocumentUri.t;
  init_vs : Vernacstate.t;
  opts : Coqargs.injection_command list;
  document : Document.document;
  execution_state : ExecutionManager.state;
  observe_id : observe_id;
  cancel_handle : Sel.Event.cancellation_handle option;
}

type event =
  | Execute of { (* we split the computation to help interruptibility *)
      id : Types.sentence_id; (* sentence of interest *)
      vst_for_next_todo : Vernacstate.t; (* the state to be used for the next
        todo, it is not necessarily the state of the last sentence, since it
        may have failed and this is a surrogate used for error resiliancy *)
      task : ExecutionManager.prepared_task;
      started : float; (* time *)
    }
  | ExecutionManagerEvent of ExecutionManager.event
  | ParseEvent
  | Observe of Types.sentence_id
  | ParseMore of Document.event
  | SendProofView of Types.sentence_id
  | SendBlockOnError of Types.sentence_id
  | SendMoveCursor of Range.t

type handled_event = {
    state : state option;
    events: event Sel.Event.t list;
    update_view: bool;
    notification: Notification.Server.t option;
}

let pp_event fmt = function
  | Execute { id; started; _ } ->
      let time = Unix.gettimeofday () -. started in 
      Stdlib.Format.fprintf fmt "ExecuteToLoc %d (started %2.3f ago)" (Stateid.to_int id) time
  | ExecutionManagerEvent _ -> Stdlib.Format.fprintf fmt "ExecutionManagerEvent"
  | ParseEvent ->
    Stdlib.Format.fprintf fmt "ParseEvent"
  | Observe id ->
    Stdlib.Format.fprintf fmt "Observe %d" (Stateid.to_int id)
  | ParseMore _ -> Stdlib.Format.fprintf fmt "ParseMore event"
  | SendProofView id ->
    Stdlib.Format.fprintf fmt "SendProofView %d" @@ (Stateid.to_int id)
  | SendBlockOnError id ->
    Stdlib.Format.fprintf fmt "SendBlockOnError %d" @@ (Stateid.to_int id)
  | SendMoveCursor range ->
    Stdlib.Format.fprintf fmt "SendBlockOnError %s" @@ (Range.to_string range)

let inject_em_event x = Sel.Event.map (fun e -> ExecutionManagerEvent e) x
let inject_em_events events = List.map inject_em_event events
let inject_doc_event x = Sel.Event.map (fun e -> ParseMore e) x
let inject_doc_events events = List.map inject_doc_event events
let mk_proof_view_event id =
  Sel.now ~priority:PriorityManager.proof_view (SendProofView (id))
let mk_observe_event id =
  Sel.now ~priority:PriorityManager.execution (Observe id)
let mk_move_cursor_event id = 
  let priority = PriorityManager.move_cursor in
  Sel.now ~priority @@ SendMoveCursor id
let mk_block_on_error_event last_range error_id =
  let priority = PriorityManager.move_cursor in
  let event = Sel.now ~priority @@ SendBlockOnError error_id in
  match last_range with
  | None ->
    [event] @ [mk_proof_view_event error_id]
  | Some range ->
    [event] @ [mk_move_cursor_event range] @ [mk_proof_view_event error_id]

type events = event Sel.Event.t list

let executed_ranges st mode =
  match st.observe_id, mode with
  | _, Settings.Mode.Continuous -> ExecutionManager.overview st.execution_state
  | Top, Settings.Mode.Manual -> empty_overview
  | Id id, Settings.Mode.Manual ->
      let range = Document.range_of_id st.document id in
      ExecutionManager.overview_until_range st.execution_state range

let observe_id_range st = 
  let doc = Document.raw_document st.document in
  match st.observe_id with
    | Top -> None
    | Id id -> match Document.get_sentence st.document id with
      | None -> failwith "observe_id does not exist"
      | Some { start; stop } ->
      let start = RawDocument.position_of_loc doc start in 
      let end_ = RawDocument.position_of_loc doc stop in 
      let range = Range.{ start; end_ } in 
      Some range

let make_diagnostic doc range oloc message severity code =
  let range =
    match oloc with
    | None -> range
    | Some loc ->
      RawDocument.range_of_loc (Document.raw_document doc) loc
  in
  let code, data =
    match code with
    | None -> None, None
    | Some (x,z) -> Some x, Some z in
  Diagnostic.create ?code ?data ~range ~message ~severity ()

let mk_diag st (id,(lvl,oloc,qf,msg)) =
  let code = 
    match qf with
    | [] -> None
    | qf ->
      let code : Jsonrpc.Id.t * Lsp.Import.Json.t =
        let open Lsp.Import.Json in
        (`String "quickfix-replace",
        qf |> yojson_of_list
        (fun qf ->
            let s = Pp.string_of_ppcmds @@ Quickfix.pp qf in
            let loc = Quickfix.loc qf in
            let range = RawDocument.range_of_loc (Document.raw_document st.document) loc in
            QuickFixData.yojson_of_t (QuickFixData.{range; text = s})
        ))
        in
      Some code
    in
    let lvl = DiagnosticSeverity.of_feedback_level lvl in
    make_diagnostic st.document (Document.range_of_id st.document id) oloc (Pp.string_of_ppcmds msg) lvl code

let mk_error_diag st (id,(oloc,msg,qf)) = (* mk_diag st (id,(Feedback.Error,oloc, msg)) *)
  let code = 
    match qf with
    | None -> None
    | Some qf ->
      let code : Jsonrpc.Id.t * Lsp.Import.Json.t =
        let open Lsp.Import.Json in
        (`String "quickfix-replace",
        qf |> yojson_of_list
        (fun qf ->
            let s = Pp.string_of_ppcmds @@ Quickfix.pp qf in
            let loc = Quickfix.loc qf in
            let range = RawDocument.range_of_loc (Document.raw_document st.document) loc in
            QuickFixData.yojson_of_t (QuickFixData.{range; text = s})
        ))
        in
      Some code
  in
  let lvl = DiagnosticSeverity.of_feedback_level Feedback.Error in
  make_diagnostic st.document (Document.range_of_id st.document id) oloc (Pp.string_of_ppcmds msg) lvl code


let mk_parsing_error_diag st Document.{ msg = (oloc,msg); start; stop; qf } =
  let doc = Document.raw_document st.document in
  let severity = DiagnosticSeverity.Error in
  let start = RawDocument.position_of_loc doc start in
  let end_ = RawDocument.position_of_loc doc stop in
  let range = Range.{ start; end_ } in
  let code = 
    match qf with
    | None -> None
    | Some qf ->
      let code : Jsonrpc.Id.t * Lsp.Import.Json.t =
        let open Lsp.Import.Json in
        (`String "quickfix-replace",
         qf |> yojson_of_list
         (fun qf ->
            let s = Pp.string_of_ppcmds @@ Quickfix.pp qf in
            let loc = Quickfix.loc qf in
            let range = RawDocument.range_of_loc (Document.raw_document st.document) loc in
            QuickFixData.yojson_of_t (QuickFixData.{range; text = s})
        ))
        in
      Some code
  in
  make_diagnostic st.document range oloc msg severity code

let all_diagnostics st =
  let parse_errors = Document.parse_errors st.document in
  let all_exec_errors = ExecutionManager.all_errors st.execution_state in
  let all_feedback = ExecutionManager.all_feedback st.execution_state in
  (* we are resilient to a state where invalidate was not called yet *)
  let exists (id,_) = Option.has_some (Document.get_sentence st.document id) in
  let not_info (_, (lvl, _, _, _)) = 
    match lvl with
    | Feedback.Info -> false
    | _ -> true
  in
  let exec_errors = all_exec_errors |> List.filter exists in
  let feedback = all_feedback |> List.filter exists |> List.filter not_info in
  List.map (mk_parsing_error_diag st) parse_errors @
    List.map (mk_error_diag st) exec_errors @
    List.map (mk_diag st) feedback

let id_of_pos st pos =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match Document.find_sentence_before st.document loc with
  | None -> None
  | Some { id } -> Some id

let id_of_sentence_after_pos st pos =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  (* if the current loc falls squarely within a sentence *)
  match Document.find_sentence st.document loc with
  | Some { id } -> Some id
  | None -> 
    (** otherwise the sentence start is after the loc,
        so we must be in the whitespace before the sentence
        and need to interpret to the sentence before instead
    *)
    match Document.find_sentence_before st.document loc with
    | None -> None
    | Some { id } -> Some id

let id_of_pos_opt st = function
  | None -> begin match st.observe_id with  Top -> None | Id id -> Some id end
  | Some pos -> id_of_pos st pos

let get_messages st id =
  let error = ExecutionManager.error st.execution_state id in
  let feedback = ExecutionManager.feedback st.execution_state id in
  let feedback = List.map (fun (lvl,_oloc,_,msg) -> DiagnosticSeverity.of_feedback_level lvl, pp_of_coqpp msg) feedback  in
  match error with
  | Some (_oloc,msg) -> (DiagnosticSeverity.Error, pp_of_coqpp msg) :: feedback
  | None -> feedback

let get_info_messages st pos =
  match id_of_pos_opt st pos with
  | None -> log "get_messages: Could not find id";[]
  | Some id -> log "get_messages: Found id";
    let info (lvl, _, _, _) = 
      match lvl with
      | Feedback.Info -> true
      | _ -> false
    in
    let feedback = ExecutionManager.feedback st.execution_state id in
    let feedback = feedback |> List.filter info in
    List.map (fun (lvl,_oloc,_,msg) -> DiagnosticSeverity.of_feedback_level lvl, pp_of_coqpp msg) feedback

let create_execution_event background event =
  let priority = if background then None else Some PriorityManager.execution in
  Sel.now ?priority event

let state_before_error state error_id =
  match Document.get_sentence state.document error_id with
  | None -> state, None
  | Some { start } ->
    match Document.find_sentence_before state.document start with
    | None ->
      let start = Position.{line=0; character=0} in
      let end_ = Position.{line=0; character=0} in
      let last_range = Range.{start; end_} in
      let observe_id = Top in
      {state with observe_id}, Some last_range
    | Some { id } ->
      let last_range = Document.range_of_id_with_blank_space state.document id in
      let observe_id = (Id id) in
      {state with observe_id}, Some last_range

let observe ~background state id ~should_block_on_error : (state * event Sel.Event.t list) =
  match Document.get_sentence state.document id with
  | None -> state, [] (* TODO error? *)
  | Some { id } ->
    Option.iter Sel.Event.cancel state.cancel_handle;
    let vst_for_next_todo, execution_state, task, error_id = ExecutionManager.build_tasks_for state.document (Document.schedule state.document) state.execution_state id should_block_on_error in
    match task with
    | Some task -> (* task will only be Some if there is no error *)
        let event = create_execution_event background (Execute {id; vst_for_next_todo; task; started = Unix.gettimeofday ()}) in
        let cancel_handle = Some (Sel.Event.get_cancellation_handle event) in
        {state with execution_state; cancel_handle}, [event]
    | None ->
      match error_id with
      | None ->
        {state with execution_state}, []
      | Some error_id ->
        let state, last_range = state_before_error state error_id in
        let events = mk_block_on_error_event last_range error_id in
        {state with execution_state}, events

let reset_to_top st = { st with observe_id = Top }

let get_document_symbols st =
  let outline = Document.outline st.document in
  let to_document_symbol elem =
    let Document.{name; statement; range; type_} = elem in
    let kind = begin match type_ with
    | TheoremKind _ -> SymbolKind.Function
    | DefinitionType _ -> SymbolKind.Variable
    | Other -> SymbolKind.Null
    end in
    DocumentSymbol.{name; detail=(Some statement); kind; range; selectionRange=range; children=None; deprecated=None; tags=None;}
  in
  List.map to_document_symbol outline

let interpret_to st id ~check_mode =
  let observe_id = (Id id) in
  let st = { st with observe_id} in
  match check_mode with
  | Settings.Mode.Manual ->
    let event = mk_observe_event id in
    let pv_event = mk_proof_view_event id in
    st, [event] @ [pv_event]
  | Settings.Mode.Continuous ->
    match ExecutionManager.is_executed st.execution_state id with
    | true -> st, [mk_proof_view_event id]
    | false -> st, []

let interpret_to_next_position st pos ~check_mode =
  match id_of_sentence_after_pos st pos with
  | None -> (st, []) (* document is empty *)
  | Some id ->
    let st, events = interpret_to st id ~check_mode in
    (st, events)

let interpret_to_position st pos ~check_mode ~point_interp_mode =
  match point_interp_mode with
  | Settings.PointInterpretationMode.Cursor ->
    begin match id_of_pos st pos with
    | None -> (st, []) (* document is empty *)
    | Some id -> interpret_to st id ~check_mode
    end
  | Settings.PointInterpretationMode.NextCommand ->
    interpret_to_next_position st pos ~check_mode

let get_next_range st pos =
  match id_of_pos st pos with
  | None -> None
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> None
    | Some { stop } ->
      match Document.find_sentence_after st.document (stop+1) with
      | None -> Some (Document.range_of_id st.document id)
      | Some { id } -> Some (Document.range_of_id st.document id)

let get_previous_range st pos =
  match id_of_pos st pos with
  | None -> None
  | Some id ->
    match Document.get_sentence st.document id with
    | None -> None
    | Some { start } ->
      match Document.find_sentence_before st.document (start) with
      | None -> Some (Document.range_of_id st.document id)
      | Some { id } -> Some (Document.range_of_id st.document id)

let interpret_to_previous st ~check_mode =
  match st.observe_id with
  | Top -> (st, [])
  | (Id id) ->
    match Document.get_sentence st.document id with
    | None -> (st, []) (* TODO error? *)
    | Some { start } ->
      match Document.find_sentence_before st.document start with
      | None -> 
        Vernacstate.unfreeze_full_state st.init_vs;
        let range = Range.top () in
        { st with observe_id=Top }, [mk_move_cursor_event range]
      | Some { id } -> 
        let st, events = interpret_to st id ~check_mode in
        let range = Document.range_of_id st.document id in
        let mv_cursor = mk_move_cursor_event range in
        st, [mv_cursor] @ events

let interpret_to_next st ~check_mode =
  match st.observe_id with
  | Top ->
    begin match Document.get_first_sentence st.document with
    | None -> st, [] (*The document is empty*)
    | Some { id } -> 
      let st, events = interpret_to st id ~check_mode in
      let range = Document.range_of_id st.document id in
      let mv_cursor = mk_move_cursor_event range in
      st, [mv_cursor] @ events
    end
  | Id id ->
    match Document.get_sentence st.document id with
    | None -> st, [] (* TODO error? *)
    | Some { stop } ->
      match Document.find_sentence_after st.document (stop+1) with
      | None -> st, []
      | Some { id } -> 
        let st, events = interpret_to st id ~check_mode in
        let range = Document.range_of_id st.document id in
        let mv_cursor = mk_move_cursor_event range in
        st, [mv_cursor] @ events

let interpret_to_end st ~check_mode =
  match Document.get_last_sentence st.document with
  | None -> (st, [])
  | Some {id} -> 
    log ("interpret_to_end id = " ^ Stateid.to_string id);
    interpret_to st id ~check_mode

let interpret_in_background st ~should_block_on_error =
  match Document.get_last_sentence st.document with
  | None -> (st, [])
  | Some {id} -> log ("interpret_to_end id = " ^ Stateid.to_string id); observe ~background:true st id ~should_block_on_error

let is_above st id1 id2 =
  let range1 = Document.range_of_id st id1 in
  let range2 = Document.range_of_id st id2 in
  Position.compare range1.start range2.start < 0

let validate_document state (Document.{unchanged_id; invalid_ids; previous_document; parsed_document}) =
  let state = {state with document=parsed_document} in
  let observe_id = match unchanged_id, state.observe_id with
    | None, Id _ -> Top
    | _, Top -> Top
    | Some id, Id id' -> if is_above previous_document id id' then (Id id) else state.observe_id
  in
  let execution_state =
    List.fold_left (fun st id ->
      ExecutionManager.invalidate previous_document (Document.schedule previous_document) id st
      ) state.execution_state (Stateid.Set.elements invalid_ids) in
  let execution_state = ExecutionManager.reset_overview execution_state previous_document in
  { state with  execution_state; observe_id }

[%%if coq = "8.18" || coq = "8.19"]
let start_library top opts = Coqinit.start_library ~top opts
[%%else]
let start_library top opts =
  let intern = Vernacinterp.fs_intern in
  Coqinit.start_library ~intern ~top opts;
[%%endif]

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
let dirpath_of_top = Coqargs.dirpath_of_top
[%%else]
let dirpath_of_top = Coqinit.dirpath_of_top
[%%endif]

let init init_vs ~opts uri ~text =
  Vernacstate.unfreeze_full_state init_vs;
  let top = try (dirpath_of_top (TopPhysical (DocumentUri.to_path uri))) with
    e -> raise e
  in
  start_library top opts;
  let init_vs = Vernacstate.freeze_full_state () in
  let document = Document.create_document init_vs.Vernacstate.synterp text in
  let execution_state, feedback = ExecutionManager.init init_vs in
  let state = { uri; opts; init_vs; document; execution_state; observe_id=Top; cancel_handle = None } in
  let priority = Some PriorityManager.launch_parsing in
  let event = Sel.now ?priority ParseEvent in
  state, [event] @ [inject_em_event feedback]

let reset { uri; opts; init_vs; document; execution_state; } =
  let text = RawDocument.text @@ Document.raw_document document in
  Vernacstate.unfreeze_full_state init_vs;
  let document = Document.create_document init_vs.synterp text in
  ExecutionManager.destroy execution_state;
  let execution_state, feedback = ExecutionManager.init init_vs in
  let observe_id = Top in
  let state = { uri; opts; init_vs; document; execution_state; observe_id; cancel_handle = None } in
  let priority = Some PriorityManager.launch_parsing in
  let event = Sel.now ?priority ParseEvent in
  state, [event] @ [inject_em_event feedback]

let apply_text_edits state edits =
  let apply_edit_and_shift_diagnostics_locs_and_overview state (range, new_text as edit) =
    let document = Document.apply_text_edit state.document edit in
    let exec_st = state.execution_state in
    let edit_start = RawDocument.loc_of_position (Document.raw_document state.document) range.Range.start in
    let edit_stop = RawDocument.loc_of_position (Document.raw_document state.document) range.Range.end_ in
    let edit_length = edit_stop - edit_start in
    let exec_st = ExecutionManager.shift_diagnostics_locs exec_st ~start:edit_stop ~offset:(String.length new_text - edit_length) in
    let execution_state = ExecutionManager.shift_overview exec_st ~before:(Document.raw_document state.document) ~after:(Document.raw_document document) ~start:edit_stop ~offset:(String.length new_text - edit_length) in
    {state with execution_state; document}
  in
  let state = List.fold_left apply_edit_and_shift_diagnostics_locs_and_overview state edits in
  let priority = Some PriorityManager.launch_parsing in
  let sel_event = Sel.now ?priority ParseEvent in
  state, [sel_event]

let execution_finished st id started =
  let time = Unix.gettimeofday () -. started in
  log (Printf.sprintf "ExecuteToLoc %d ends after %2.3f" (Stateid.to_int id) time);
  (* We update the state to trigger a publication of diagnostics *)
  let update_view = true in
  let state = Some st in
  {state; events=[]; update_view; notification=None}

let execute st id vst_for_next_todo started task background block =
  let time = Unix.gettimeofday () -. started in
  match Document.get_sentence st.document id with
  | None ->
    log (Printf.sprintf "ExecuteToLoc %d stops after %2.3f, sentences invalidated" (Stateid.to_int id) time);
    {state=Some st; events=[]; update_view=true; notification=None} (* Sentences have been invalidate, probably because the user edited while executing *)
  | Some _ ->
    log (Printf.sprintf "ExecuteToLoc %d continues after %2.3f" (Stateid.to_int id) time);
    let (next, execution_state,vst_for_next_todo,events, exec_error) =
      ExecutionManager.execute st.execution_state st.document (vst_for_next_todo, [], false) task block in
    let st, block_events =
      match exec_error with
      | None -> st, []
      | Some error_id -> let st, last_range = state_before_error st error_id in
        let events = if block then mk_block_on_error_event last_range error_id else [] in
        st, events
      in
    let event = Option.map (fun task -> create_execution_event background (Execute {id; vst_for_next_todo; task; started })) next in
    match event, block_events with
      | None, [] -> execution_finished { st with execution_state } id started (* There is no new tasks, and no errors -> execution finished *)
      | _ ->
        let cancel_handle = Option.map Sel.Event.get_cancellation_handle event in
        let event = Option.cata (fun event -> [event]) [] event in
        let state = Some {st with execution_state; cancel_handle} in
        let update_view = true in
        let events = inject_em_events events @ block_events @ event in
        {state; events; update_view; notification=None}

let get_proof st diff_mode id =
  let previous_st id =
    let oid = fst @@ Scheduler.task_for_sentence (Document.schedule st.document) id in
    Option.bind oid (ExecutionManager.get_vernac_state st.execution_state)
  in
  let observe_id = to_sentence_id st.observe_id in
  let oid = Option.append id observe_id in
  let ost = Option.bind oid (ExecutionManager.get_vernac_state st.execution_state) in
  let previous = Option.bind oid previous_st in
  Option.bind ost (ProofState.get_proof ~previous diff_mode)

let handle_execution_manager_event st ev =
  let id, execution_state_update, events = ExecutionManager.handle_event ev st.execution_state in
  let st = 
    match (id, execution_state_update) with
    | Some id, Some exec_st ->
      let execution_state = ExecutionManager.update_processed id exec_st st.document in
      Some {st with execution_state}
    | Some id, None ->
      let execution_state = ExecutionManager.update_processed id st.execution_state st.document in
      Some {st with execution_state}
    | _, _ -> Option.map (fun execution_state -> {st with execution_state}) execution_state_update
  in
  let update_view = true in
  {state=st; events=(inject_em_events events); update_view; notification=None}

let handle_event ev st ~block ~background diff_mode =
  match ev with
  | Execute { id; vst_for_next_todo; started; task } ->
    execute st id vst_for_next_todo started task background block
  | ExecutionManagerEvent ev ->
    handle_execution_manager_event st ev
  | Observe id ->
    let update_view = true in
    let st, events = observe st id ~should_block_on_error:block ~background in
    {state=Some st; events; update_view; notification=None}
  | ParseEvent ->
    let document, events = Document.validate_document st.document in
    let update_view = true in
    let state = Some {st with document} in
    let events = inject_doc_events events in
    {state; events; update_view; notification=None}
  | ParseMore ev ->
    let document, events, parsing_end_info = Document.handle_event st.document ev in
    begin match parsing_end_info with
    | None ->
      let update_view = false in
      let state = Some {st with document} in
      let events = inject_doc_events events in
      {state; events; update_view; notification=None}
    | Some parsing_end_info ->
      let st = validate_document st parsing_end_info in
      let update_view = true in
      if background then
        let (st, events) = interpret_in_background st ~should_block_on_error:block in
        {state=(Some st); events; update_view; notification=None}
      else
        {state=(Some st); events=[]; update_view; notification=None}
    end
  | SendProofView id ->
    let proof = get_proof st diff_mode (Some id) in
    let messages = get_messages st id in
    let params = Notification.Server.ProofViewParams.{ proof; messages} in
    let notification = Some (Notification.Server.ProofView params) in
    let update_view = true in
    {state=(Some st); events=[]; update_view; notification}
  | SendBlockOnError id ->
    let {uri} = st in
    let range = Document.range_of_id st.document id in
    let notification = Some (Notification.Server.BlockOnError {uri; range}) in
    {state=(Some st); events=[]; update_view=false; notification}
  | SendMoveCursor range ->
    let {uri} = st in
    let notification = Some (Notification.Server.MoveCursor {uri; range}) in
    {state=(Some st); events=[]; update_view=false; notification}

let context_of_id st = function
  | None -> Some (ExecutionManager.get_initial_context st.execution_state)
  | Some id -> ExecutionManager.get_context st.execution_state id

(** Get context at the start of the sentence containing [pos] *)
let get_context st pos = context_of_id st (id_of_pos st pos)

let get_completions st pos =
  match id_of_pos st pos with
  | None -> Error ("Can't get completions, no sentence found before the cursor")
  | Some id ->
    let ost = ExecutionManager.get_vernac_state st.execution_state id in
    let settings = ExecutionManager.get_options () in
    match Option.bind ost @@ CompletionSuggester.get_completions settings.completion_options with
    | None -> Error ("Can't get completions")
    | Some lemmas -> Ok (lemmas)

[%%if coq = "8.18" || coq = "8.19"]
[%%elif coq = "8.20"]
  let parsable_make = Pcoq.Parsable.make
  let unfreeze = Pcoq.unfreeze
  let entry_parse = Pcoq.Entry.parse
[%%else]
  let parsable_make = Procq.Parsable.make
  let unfreeze = Procq.unfreeze
  let entry_parse = Procq.Entry.parse
[%%endif]

[%%if coq = "8.18" || coq = "8.19"]
let parse_entry st pos entry pattern =
  let pa = Pcoq.Parsable.make (Gramlib.Stream.of_string pattern) in
  let st = match Document.find_sentence_before st.document pos with
  | None -> st.init_vs.Vernacstate.synterp.parsing
  | Some { synterp_state } -> synterp_state.Vernacstate.Synterp.parsing
  in
  Vernacstate.Parser.parse st entry pa
[%%else]
let parse_entry st pos entry pattern =
  let pa = parsable_make (Gramlib.Stream.of_string pattern) in
  let st = match Document.find_sentence_before st.document pos with
  | None -> Vernacstate.(Synterp.parsing st.init_vs.synterp)
  | Some { synterp_state } -> Vernacstate.Synterp.parsing synterp_state
  in  
  unfreeze st;
  entry_parse entry pa
[%%endif]

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let smart_global = Pcoq.Prim.smart_global
[%%else]
  let smart_global = Procq.Prim.smart_global
[%%endif]

let about st pos ~pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma, env) ->
    try
      let ref_or_by_not = parse_entry st loc (smart_global) pattern in
      let udecl = None (* TODO? *) in
      Ok (pp_of_coqpp @@ Prettyp.print_about env sigma ref_or_by_not udecl)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

let search st ~id pos pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> [] (* TODO execute? *)
  | Some (sigma, env) ->
    let query, r = parse_entry st loc (G_vernac.search_queries) pattern in
    SearchQuery.interp_search ~id env sigma query r

(** Try to generate hover text from [pattern] the context of the given [sentence] *)
let hover_of_sentence st loc pattern sentence = 
  match context_of_id st (Option.map (fun ({ id; _ }: Document.sentence) -> id) sentence) with
  | None -> log "hover: no context found"; None
  | Some (sigma, env) ->
    try
      let ref_or_by_not = parse_entry st loc (smart_global) pattern in
      Language.Hover.get_hover_contents env sigma ref_or_by_not
    with e ->
      let e, info = Exninfo.capture e in
      log ("Exception while handling hover: " ^ (Pp.string_of_ppcmds @@ CErrors.iprint (e, info)));
      None

let hover st pos =
  (* Tries to get hover at three difference places:
     - At the start of the current sentence
     - At the start of the next sentence (for symbols defined in the current sentence)
       e.g. Definition, Inductive
     - At the next QED (for symbols defined after proof), if the next sentence 
       is in proof mode e.g. Lemmas, Definition with tactics *)
  let opattern = RawDocument.word_at_position (Document.raw_document st.document) pos in
  match opattern with
  | None -> log "hover: no word found at cursor"; None
  | Some pattern ->
    log ("hover: found word at cursor: \"" ^ pattern ^ "\"");
    let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
    (* hover at previous sentence *)
    match hover_of_sentence st loc pattern (Document.find_sentence_before st.document loc) with
    | Some _ as x -> x
    | None -> 
    match Document.find_sentence_after st.document loc with
    | None -> None (* Skip if no next sentence *)
    | Some sentence as opt ->
    (* hover at next sentence *)
    match hover_of_sentence st loc pattern opt with
    | Some _ as x -> x
    | None -> 
    match sentence.ast.classification with
    (* next sentence in proof mode, hover at qed *)
    | VtProofStep _ | VtStartProof _ -> 
        hover_of_sentence st loc pattern (Document.find_next_qed st.document loc)
    | _ -> None

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let lconstr = Pcoq.Constr.lconstr
[%%else]
  let lconstr = Procq.Constr.lconstr
[%%endif]

let check st pos ~pattern =
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma,env) ->
    let rc = parse_entry st loc lconstr pattern in
    try
      let redexpr = None in
      Ok (pp_of_coqpp @@ Vernacentries.check_may_eval env sigma redexpr rc)
    with e ->
      let e, info = Exninfo.capture e in
      Error (Pp.string_of_ppcmds @@ CErrors.iprint (e, info))

[%%if coq = "8.18" || coq = "8.19"]
let print_located_qualid _ qid = Prettyp.print_located_qualid qid
[%%else]
let print_located_qualid = Prettyp.print_located_qualid
[%%endif]

let locate st pos ~pattern = 
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> Error ("No context found") (*TODO execute *)
  | Some (sigma, env) ->
    match parse_entry st loc (smart_global) pattern with
    | { v = AN qid } -> Ok (pp_of_coqpp @@ print_located_qualid env qid)
    | { v = ByNotation (ntn, sc)} ->
      Ok( pp_of_coqpp @@ Notation.locate_notation
        (Constrextern.without_symbols (Printer.pr_glob_constr_env env sigma)) ntn sc)

[%%if coq = "8.18" || coq = "8.19"]
  let print_name = Prettyp.print_name
[%%else]
  let print_name =
    let access = Library.indirect_accessor[@@warning "-3"] in
    Prettyp.print_name access
[%%endif]

let print st pos ~pattern = 
  let loc = RawDocument.loc_of_position (Document.raw_document st.document) pos in
  match get_context st pos with
  | None -> Error("No context found")
  | Some (sigma, env) ->
    let qid = parse_entry st loc (smart_global) pattern in
    let udecl = None in (*TODO*)
    Ok ( pp_of_coqpp @@ print_name env sigma qid udecl )
    
module Internal = struct

  let document st =
    st.document

  let raw_document st = 
    Document.raw_document st.document

  let execution_state st =
    st.execution_state

  let observe_id st =
    match st.observe_id with
    | Top -> None
    | (Id id) -> Some id

  let validate_document st parsing_end_info = validate_document st parsing_end_info

  let string_of_state st =
    let code_lines_by_id = Document.code_lines_sorted_by_loc st.document in
    let code_lines_by_end = Document.code_lines_by_end_sorted_by_loc st.document in
    let string_of_state id =
      if ExecutionManager.is_executed st.execution_state id then "(executed)"
      else if ExecutionManager.is_remotely_executed st.execution_state id then "(executed in worker)"
      else "(not executed)"
    in
    let string_of_item item =
      Document.Internal.string_of_item item ^ " " ^
        match item with
        | Sentence { id } -> string_of_state id
        | ParsingError _ -> "(error)"
        | Comment _ -> "(comment)"
    in
    let string_by_id = String.concat "\n" @@ List.map string_of_item code_lines_by_id in
    let string_by_end = String.concat "\n" @@ List.map string_of_item code_lines_by_end in
    String.concat "\n" ["Document using sentences_by_id map\n"; string_by_id; "\nDocument using sentences_by_end map\n"; string_by_end]
    let inject_doc_events = inject_doc_events

end
