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

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

open Printer
open Lsp.Types
open Protocol
open Protocol.LspWrapper
open Protocol.ExtProtocol

module CompactedDecl = Context.Compacted.Declaration

let init_state : Vernacstate.t option ref = ref None
let get_init_state () =
  match !init_state with
  | Some st -> st
  | None -> CErrors.anomaly Pp.(str "Initial state not available")

type tab = { st : Dm.DocumentManager.state; visible : bool }

let states : (string, tab) Hashtbl.t = Hashtbl.create 39

let check_mode = ref Settings.Mode.Manual

let diff_mode = ref Settings.Goals.Diff.Mode.Off
let max_memory_usage  = ref 4000000000

let full_diagnostics = ref false
let full_messages = ref false

let point_interp_mode = ref Settings.PointInterpretationMode.Cursor

let block_on_first_error = ref true

let Dm.Types.Log log = Dm.Log.mk_log "lspManager"

let conf_request_id = max_int

let server_info = InitializeResult.create_serverInfo
  ~name:"vscoq-language-server"
  ~version:"2.2.1"
  ()

type lsp_event = 
  | Receive of Jsonrpc.Packet.t option
  | Send of Jsonrpc.Packet.t

type event =
 | LspManagerEvent of lsp_event
 | DocumentManagerEvent of DocumentUri.t * Dm.DocumentManager.event
 | Notification of notification
 | LogEvent of Dm.Log.event

type events = event Sel.Event.t list

let lsp : event Sel.Event.t =
  Sel.On.httpcle ~priority:Dm.PriorityManager.lsp_message ~name:"lsp" Unix.stdin (function
    | Ok buff ->
      begin
        log "UI req ready";
        try LspManagerEvent (Receive (Some (Jsonrpc.Packet.t_of_yojson (Yojson.Safe.from_string (Bytes.to_string buff)))))
        with exn ->
          log @@ "failed to decode json";
          LspManagerEvent (Receive None)
      end
    | Error exn ->
        log @@ ("failed to read message: " ^ Printexc.to_string exn);
        (* do not remove this line otherwise the server stays running in some scenarios *)
        exit 0)


let output_json obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log @@ "sent: " ^ msg;
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

let output_notification notif =
  output_json @@ Jsonrpc.Notification.yojson_of_t @@ Notification.Server.to_jsonrpc notif

let inject_dm_event uri x : event Sel.Event.t =
  Sel.Event.map (fun e -> DocumentManagerEvent(uri,e)) x

let inject_notification x : event Sel.Event.t =
  Sel.Event.map (fun x -> Notification(x)) x

let inject_debug_event x : event Sel.Event.t =
  Sel.Event.map (fun x -> LogEvent x) x

let inject_dm_events (uri,l) =
  List.map (inject_dm_event uri) l

let inject_notifications l =
  List.map inject_notification l

let inject_debug_events l =
  List.map inject_debug_event l

let do_configuration settings = 
  let open Settings in
  let open Dm.ExecutionManager in
  let delegation_mode =
    match settings.proof.delegation with
    | None     -> CheckProofsInMaster
    | Skip     -> SkipProofs
    | Delegate -> DelegateProofsToWorkers { number_of_workers = Option.get settings.proof.workers }
  in
  Dm.ExecutionManager.set_options {
    delegation_mode;
    completion_options = settings.completion;
    enableDiagnostics = settings.diagnostics.enable;
  };
  check_mode := settings.proof.mode;
  diff_mode := settings.goals.diff.mode;
  full_diagnostics := settings.diagnostics.full;
  full_messages := settings.goals.messages.full;
  max_memory_usage := settings.memory.limit * 1000000000;
  block_on_first_error := settings.proof.block;
  point_interp_mode := settings.proof.pointInterpretationMode

let send_configuration_request () =
  let id = `Int conf_request_id in
  let mk_configuration_item section =
    ConfigurationItem.({ scopeUri = None; section = Some section })
  in
  let items = List.map mk_configuration_item ["vscoq"] in
  let req = Lsp.Server_request.(to_jsonrpc_request (WorkspaceConfiguration { items }) ~id) in
  Send (Request req)

let do_initialize id params =
  let Lsp.Types.InitializeParams.{ initializationOptions } = params in
  begin match initializationOptions with
  | None -> log "Failed to decode initialization options"
  | Some initializationOptions ->
    do_configuration @@ Settings.t_of_yojson initializationOptions;
  end;
  let textDocumentSync = `TextDocumentSyncKind TextDocumentSyncKind.Incremental in
  let completionProvider = CompletionOptions.create ~resolveProvider:false () in
  let documentSymbolProvider = `Bool true in
  let hoverProvider = `Bool true in
  let capabilities = ServerCapabilities.create
    ~textDocumentSync
    ~completionProvider
    ~hoverProvider
    ~documentSymbolProvider
  ()
  in
  let initialize_result = Lsp.Types.InitializeResult.{
    capabilities = capabilities; 
    serverInfo = Some server_info;
  } in
  log "---------------- initialized --------------";
  let debug_events = Dm.Log.lsp_initialization_done () |> inject_debug_events in
  Ok initialize_result, debug_events@[Sel.now @@ LspManagerEvent (send_configuration_request ())]

let do_shutdown id params =
  Ok(()), []

let do_exit () =
  exit 0

let parse_loc json =
  let open Yojson.Safe.Util in
  let line = json |> member "line" |> to_int in
  let character = json |> member "character" |> to_int in
  Position.{ line ; character }

let publish_diagnostics uri doc =
  let diagnostics = Dm.DocumentManager.all_diagnostics doc in
  let diagnostics =
    if !full_diagnostics then diagnostics
    else List.filter (fun d -> d.Diagnostic.severity != Some DiagnosticSeverity.Information) diagnostics
  in
  let params = Lsp.Types.PublishDiagnosticsParams.create ~diagnostics ~uri () in
  let diag_notification = Lsp.Server_notification.PublishDiagnostics params in
  output_notification (Std diag_notification)

let send_highlights uri doc =
  let { Dm.Types.processing;  processed; prepared } =
    Dm.DocumentManager.executed_ranges doc !check_mode in
  let notification = Notification.Server.UpdateHighlights {
    uri;
    preparedRange = prepared;
    processingRange = processing;
    processedRange = processed;
  }
  in
  output_json @@ Jsonrpc.Notification.yojson_of_t @@ Notification.Server.to_jsonrpc notification

let send_proof_view pv =
  log "-------------------------- sending proof view ---------------------------------------";
  let notification = Notification.Server.ProofView pv in
  output_json @@ Jsonrpc.Notification.yojson_of_t @@ Notification.Server.to_jsonrpc notification

let send_move_cursor uri range = 
  let notification = Notification.Server.MoveCursor {uri;range} in 
  output_notification notification

let send_block_on_error uri range = 
  let notification = Notification.Server.BlockOnError {uri;range} in 
  output_notification notification

let send_coq_debug message =
  let notification = Notification.Server.CoqLogMessage {message} in
  output_notification notification

let send_error_notification message =
  let type_ = MessageType.Error in
  let params = ShowMessageParams.{type_; message} in
  let notification = Lsp.Server_notification.ShowMessage params in
  output_json @@ Jsonrpc.Notification.yojson_of_t @@ Lsp.Server_notification.to_jsonrpc notification

let update_view uri st =
  if (Dm.ExecutionManager.is_diagnostics_enabled ()) then (
    send_highlights uri st;
    publish_diagnostics uri st;
  )

let replace_state path st visible = Hashtbl.replace states path { st; visible}

let run_documents () =
  let interpret_doc_in_bg path { st : Dm.DocumentManager.state ; visible } events =
      let st = Dm.DocumentManager.reset_to_top st in
      let (st, events') = Dm.DocumentManager.interpret_to_end st !check_mode in
      let uri = DocumentUri.of_path path in
      replace_state path st visible;
      update_view uri st;
      let events' = inject_dm_events (uri, events') in
      events@events'
  in
  Hashtbl.fold interpret_doc_in_bg states []

let reset_observe_ids =
  let reset_doc_observe_id path {st : Dm.DocumentManager.state; visible} events =
    let st = Dm.DocumentManager.reset_to_top st in
    let uri = DocumentUri.of_path path in
    replace_state path st visible;
    update_view uri st
  in
  Hashtbl.fold reset_doc_observe_id states

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
(* in these coq versions init_runtime called globally for the process includes init_document
   this means in these versions we do not support local _CoqProject except for the effect on injections
   (eg -noinit) *)
let init_document _ vst = vst
[%%else]
let init_document local_args vst =
  let () = Vernacstate.unfreeze_full_state vst in
  let () = Coqinit.init_document local_args in
  Vernacstate.freeze_full_state ()
[%%endif]

[%%if  coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let parse_args args =
    let usage = {
      Boot.Usage.executable_name = "";
      extra_args = "";
      extra_options = "";
    } in
    fst @@ Coqargs.parse_args ~init:Coqargs.default ~usage args
[%%else]
  let parse_args args =
    fst @@ Coqargs.parse_args ~init:Coqargs.default args
[%%endif]

let open_new_document uri text =
  let vst = get_init_state () in

  let local_args =
    let fname = DocumentUri.to_path uri in
    let dir = Filename.dirname fname in
    match CoqProject_file.find_project_file ~from:dir ~projfile_name:"_CoqProject" with
    | None ->
      log (Printf.sprintf "No project file found for %s" fname);
      Coqargs.default
    | Some f ->
      let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
      let args = CoqProject_file.coqtop_args_from_project project in
      log (Printf.sprintf "Arguments from project file %s: %s" f (String.concat " " args));
      parse_args args
      
  in

  let vst = init_document local_args vst in
  let st, events = try Dm.DocumentManager.init vst ~opts:(Coqargs.injection_commands local_args) uri ~text with
    e -> raise e
  in
  Hashtbl.add states (DocumentUri.to_path uri) { st ; visible = true; };
  update_view uri st;
  inject_dm_events (uri, events)

let textDocumentDidOpen params =
  let Lsp.Types.DidOpenTextDocumentParams.{ textDocument = { uri; text } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> open_new_document uri text
  | Some { st } ->
    let (st, events) = 
      if !check_mode = Settings.Mode.Continuous then
        let (st, events) = Dm.DocumentManager.interpret_to_end st !check_mode in
        (st, events)
      else 
        (st, [])
    in
    update_view uri st;
    inject_dm_events (uri, events)

let textDocumentDidChange params =
  let Lsp.Types.DidChangeTextDocumentParams.{ textDocument; contentChanges } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
    | None -> log @@ "[textDocumentDidChange] ignoring event on non-existing document"; []
    | Some { st; visible } ->
      let mk_text_edit TextDocumentContentChangeEvent.{ range; text } =
        Option.get range, text
      in
      let text_edits = List.map mk_text_edit contentChanges in
      let st, events = Dm.DocumentManager.apply_text_edits st text_edits in
      replace_state (DocumentUri.to_path uri) st visible;
      update_view uri st;
      inject_dm_events (uri, events)

let textDocumentDidSave params =
  [] (* TODO handle properly *)

let current_memory_usage () =
  let { Gc.heap_words; _ } = Gc.stat () in
  Sys.word_size * heap_words

let purge_invisible_tabs () =
  Hashtbl.filter_map_inplace (fun u ({ visible } as v) ->
    if visible then Some v
    else begin
      log @@ "purging tab " ^ u;
      None
    end)
  states

let consider_purge_invisible_tabs () =
  let usage = current_memory_usage () in
  if usage > !max_memory_usage (* 4G *) then begin
    purge_invisible_tabs ();
    let vst = get_init_state () in
    Vernacstate.unfreeze_full_state vst;
    Vernacstate.Interp.invalidate_cache ();
    Gc.compact ();
    let new_usage = current_memory_usage () in
    log @@ Printf.sprintf  "memory footprint %d -> %d" usage new_usage;
  end

let textDocumentDidClose params =
  let Lsp.Types.DidCloseTextDocumentParams.{ textDocument } = params in
  let path = DocumentUri.to_path textDocument.uri in
  begin match Hashtbl.find_opt states path with
  | None -> assert false
  | Some { st } -> replace_state path st false
  end;
  consider_purge_invisible_tabs ();
  [] (* TODO handle properly *)

let textDocumentHover id params = 
  let Lsp.Types.HoverParams.{ textDocument; position } = params in
  let open Yojson.Safe.Util in
  match Hashtbl.find_opt states (DocumentUri.to_path textDocument.uri) with
  | None -> log @@ "[textDocumentHover] ignoring event on non existing document"; Ok None (* FIXME handle error case properly *)
  | Some { st } ->
    match Dm.DocumentManager.hover st position with
    | Some contents -> Ok (Some (Hover.create ~contents:(`MarkupContent contents) ()))
    | _ -> Ok None (* FIXME handle error case properly *)

let progress_hook uri () =
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "ignoring non existent document"
  | Some { st } -> update_view uri st

let coqtopInterpretToPoint params =
  let Notification.Client.InterpretToPointParams.{ textDocument; position } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[interpretToPoint] ignoring event on non existent document"; []
  | Some { st; visible } ->
    let (st, events) = Dm.DocumentManager.interpret_to_position st position !check_mode !point_interp_mode
    in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    let sel_events = inject_dm_events (uri, events) in
    sel_events
 
let coqtopStepBackward params =
  let Notification.Client.StepBackwardParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log "[stepBackward] ignoring event on non existent document"; []
  | Some { st; visible } ->
      let (st, events) = Dm.DocumentManager.interpret_to_previous st !check_mode in
      replace_state (DocumentUri.to_path uri) st visible;
      inject_dm_events (uri,events)

let coqtopStepForward params =
  let Notification.Client.StepForwardParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log "[stepForward] ignoring event on non existent document"; []
  | Some { st; visible } ->
      let (st, events) = Dm.DocumentManager.interpret_to_next st !check_mode in
      replace_state (DocumentUri.to_path uri) st visible;
      update_view uri st;
      inject_dm_events (uri,events) 
        
  
  let make_CompletionItem i item : CompletionItem.t = 
    let (label, insertText, typ, path) = Dm.CompletionItems.pp_completion_item item in
    CompletionItem.create
      ~label
      ~insertText
      ~detail:typ
      ~documentation:(`String ("Path: " ^ path))
      ~sortText:(Printf.sprintf "%5d" i)
      ?filterText:(if label == insertText then None else Some (insertText))
      ()

let textDocumentCompletion id params =
  let return_completion ~isIncomplete ~items =
    Ok (Some (`CompletionList (Lsp.Types.CompletionList.create ~isIncomplete ~items ())))
  in
  if not (Dm.ExecutionManager.get_options ()).completion_options.enable then
    return_completion ~isIncomplete:false ~items:[], []
  else
  let Lsp.Types.CompletionParams.{ textDocument = { uri }; position } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[textDocumentCompletion]ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } -> 
    match Dm.DocumentManager.get_completions st position with
    | Ok completionItems -> 
      let items = List.mapi make_CompletionItem completionItems in
      return_completion ~isIncomplete:false ~items, []
    | Error e -> 
      let message = e in
      Error(message), []

let documentSymbol id params =
  let Lsp.Types.DocumentSymbolParams.{ textDocument = {uri}} = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[documentSymbol] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some tab -> log @@ "[documentSymbol] getting symbols";
    let symbols = Dm.DocumentManager.get_document_symbols tab.st in
    Ok(Some (`DocumentSymbol symbols)), []

let coqtopResetCoq id params =
  let Request.Client.ResetParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[resetCoq] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st; visible } -> 
    let st, events = Dm.DocumentManager.reset st in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    Ok(()), (uri,events) |> inject_dm_events

let coqtopInterpretToEnd params =
  let Notification.Client.InterpretToEndParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[interpretToEnd] ignoring event on non existent document"; []
  | Some { st; visible } ->
    let (st, events) = Dm.DocumentManager.interpret_to_end st !check_mode in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    inject_dm_events (uri,events)

let coqtopLocate id params = 
  let Request.Client.LocateParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[locate] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } ->
    Dm.DocumentManager.locate st position ~pattern, []

let coqtopPrint id params = 
  let Request.Client.PrintParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[print] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } -> Dm.DocumentManager.print st position ~pattern, []

let coqtopAbout id params =
  let Request.Client.AboutParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[about] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } -> Dm.DocumentManager.about st position ~pattern, []

let coqtopCheck id params =
  let Request.Client.CheckParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[check] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } -> Dm.DocumentManager.check st position ~pattern, []

let coqtopSearch id params =
  let Request.Client.SearchParams.{ textDocument = { uri }; id; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[search] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } ->
    try
      let notifications = Dm.DocumentManager.search st ~id position pattern in
      Ok(()), inject_notifications notifications
    with e ->
      let e, info = Exninfo.capture e in
      let message = Pp.string_of_ppcmds @@ CErrors.iprint (e, info) in
      Error(message), []

let sendDocumentState id params = 
  let Request.Client.DocumentStateParams.{ textDocument } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log @@ "[documentState] ignoring event on non existent document"; Error("Document does not exist"), []
  | Some { st } -> let document = Dm.DocumentManager.Internal.string_of_state st in
    Ok Request.Client.DocumentStateResult.{ document }, []

let workspaceDidChangeConfiguration params = 
  let Lsp.Types.DidChangeConfigurationParams.{ settings } = params in
  let settings = Settings.t_of_yojson settings in
  do_configuration settings;
  match !check_mode with
  | Continuous -> run_documents ()
  | Manual -> reset_observe_ids (); ([] : events)

let dispatch_std_request : type a. Jsonrpc.Id.t -> a Lsp.Client_request.t -> (a,string) result * events =
  fun id req ->
  match req with
  | Initialize params ->
    do_initialize id params
  | Shutdown ->
    do_shutdown id ()
  | TextDocumentCompletion params ->
    textDocumentCompletion id params
  | TextDocumentHover params ->
    textDocumentHover id params, []
  | DocumentSymbol params ->
    documentSymbol id params
  | UnknownRequest _ | _  -> Error "Received unknown request", []

let dispatch_request : type a. Jsonrpc.Id.t -> a Request.Client.t -> (a,string) result * events =
  fun id req ->
  match req with
  | Std req -> dispatch_std_request id req
  | Reset params -> coqtopResetCoq id params
  | About params -> coqtopAbout id params
  | Check params -> coqtopCheck id params
  | Locate params -> coqtopLocate id params
  | Print params -> coqtopPrint id params
  | Search params -> coqtopSearch id params
  | DocumentState params -> sendDocumentState id params

let dispatch_std_notification = 
  let open Lsp.Client_notification in function
  | TextDocumentDidOpen params -> log "Received notification: textDocument/didOpen";
    begin try textDocumentDidOpen params with
      exn -> let info = Exninfo.capture exn in
      let message = "Error while opening document. " ^ Pp.string_of_ppcmds @@ CErrors.iprint_no_report info in
      send_error_notification message; []
    end
  | TextDocumentDidChange params -> log "Received notification: textDocument/didChange";
    textDocumentDidChange params
  | TextDocumentDidClose params ->  log "Received notification: textDocument/didClose";
    textDocumentDidClose params
  | ChangeConfiguration params -> log "Received notification: workspace/didChangeConfiguration";
    workspaceDidChangeConfiguration params
  | Initialized -> []
  | Exit ->
    do_exit ()
  | UnknownNotification _ | _ -> log "Received unknown notification"; []

let dispatch_notification =
  let open Notification.Client in function
  | InterpretToPoint params -> log "Received notification: vscoq/interpretToPoint"; coqtopInterpretToPoint params 
  | InterpretToEnd params -> log "Received notification: vscoq/interpretToEnd"; coqtopInterpretToEnd params
  | StepBackward params -> log "Received notification: vscoq/stepBackward"; coqtopStepBackward params
  | StepForward params -> log "Received notification: vscoq/stepForward"; coqtopStepForward params
  | Std notif -> dispatch_std_notification notif

let handle_lsp_event = function
  | Receive None -> [lsp]
  | Receive (Some rpc) ->
    lsp :: (* the event is recurrent *)
    begin try
      begin match rpc with
      | Request req ->
          log @@ "ui request: " ^ req.method_;
          begin match Request.Client.t_of_jsonrpc req with
          | Error(e) -> log @@ "Error decoding request: " ^ e; []
          | Ok(Pack r) ->
            let resp, events = dispatch_request req.id r in
            begin match resp with
            | Error message ->
              output_json @@ Jsonrpc.Response.(yojson_of_t @@ error req.id (Error.make ~code:RequestFailed ~message ()))
            | Ok resp ->
              let resp = Request.Client.yojson_of_result r resp in
              output_json @@ Jsonrpc.Response.(yojson_of_t @@ ok req.id resp)
            end;
            events
          end
      | Notification notif ->
        begin match Notification.Client.of_jsonrpc notif with
        | Ok notif -> dispatch_notification notif
        | Error e -> log @@ "error decoding notification: " ^ e; []
        end
      | Response resp ->
          log @@ "got unknown response";
          []
      | Batch_response _ -> log "Unsupported batch response received"; []
      | Batch_call _ -> log "Unsupported batch call received"; []
      end
    with Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(exn,json) ->
      log @@ "error parsing json: " ^ Yojson.Safe.pretty_to_string json;
      []
    end
  | Send jsonrpc ->
    output_json (Jsonrpc.Packet.yojson_of_t jsonrpc); []

let pr_lsp_event = function
  | Receive jsonrpc ->
    Pp.str "Request"
  | Send jsonrpc ->
    Pp.str "Send"

let handle_event = function
  | LspManagerEvent e -> handle_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    begin match Hashtbl.find_opt states (DocumentUri.to_path uri) with
    | None ->
      log @@ "ignoring event on non-existing document";
      []
    | Some { st; visible } ->
      let handled_event = Dm.DocumentManager.handle_event e st ~block:!block_on_first_error !check_mode !diff_mode in
      let events = handled_event.events in
      begin match handled_event.state with
        | None -> ()
        | Some st ->
          replace_state (DocumentUri.to_path uri) st visible;
          if handled_event.update_view then update_view uri st
      end;
      Option.iter output_notification handled_event.notification;
      inject_dm_events (uri, events)
    end
  | Notification notification ->
    begin match notification with 
    | QueryResultNotification params ->
      output_notification @@ SearchResult params; [inject_notification Dm.SearchQuery.query_feedback]
    end
  | LogEvent e ->
    send_coq_debug e; [inject_debug_event Dm.Log.debug]

let pr_event = function
  | LspManagerEvent e -> pr_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    Pp.str @@ Format.asprintf "%a" Dm.DocumentManager.pp_event e
  | Notification _ -> Pp.str"notif"
  | LogEvent _ -> Pp.str"debug"

let init () =
  init_state := Some (Vernacstate.freeze_full_state ());
  [lsp]
