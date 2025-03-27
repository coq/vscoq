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
open Dm.Types

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
  ~version:"2.2.5"
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
        log (fun () -> "UI req ready");
        try LspManagerEvent (Receive (Some (Jsonrpc.Packet.t_of_yojson (Yojson.Safe.from_string (Bytes.to_string buff)))))
        with exn ->
          log (fun () -> "failed to decode json");
          LspManagerEvent (Receive None)
      end
    | Error exn ->
        log (fun () -> ("failed to read message: " ^ Printexc.to_string exn));
        (* do not remove this line otherwise the server stays running in some scenarios *)
        exit 0)


let output_json obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log (fun () -> "sent: " ^ msg);
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
  | None -> log (fun () -> "Failed to decode initialization options")
  | Some initializationOptions ->
    do_configuration @@ Settings.t_of_yojson initializationOptions;
  end;
  let textDocumentSync = `TextDocumentSyncKind TextDocumentSyncKind.Incremental in
  let completionProvider = CompletionOptions.create ~resolveProvider:false () in
  let documentSymbolProvider = `DocumentSymbolOptions (DocumentSymbolOptions.create ~workDoneProgress:true ()) in
  let hoverProvider = `Bool true in
  let definitionProvider = `Bool true in
  let capabilities = ServerCapabilities.create
    ~textDocumentSync
    ~completionProvider
    ~hoverProvider
    ~definitionProvider
    ~documentSymbolProvider
  ()
  in
  let initialize_result = Lsp.Types.InitializeResult.{
    capabilities = capabilities; 
    serverInfo = Some server_info;
  } in
  log (fun () -> "---------------- initialized --------------");
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
  log (fun () -> "-------------------------- sending proof view ---------------------------------------");
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
      let (st, events') = Dm.DocumentManager.interpret_in_background st ~should_block_on_error:!block_on_first_error in
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

let open_new_document uri text =
  let vst = get_init_state () in
  let fname = DocumentUri.to_path uri in
  let dir = Filename.dirname fname in
  let local_args = Args.get_local_args dir in
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
        let (st, events) = Dm.DocumentManager.interpret_in_background st ~should_block_on_error:!block_on_first_error in
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
    | None -> log (fun () -> "[textDocumentDidChange] ignoring event on non-existing document"); []
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
      log (fun () -> "purging tab " ^ u);
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
    log (fun () -> Printf.sprintf  "memory footprint %d -> %d" usage new_usage);
  end

let textDocumentDidClose params =
  let Lsp.Types.DidCloseTextDocumentParams.{ textDocument } = params in
  let path = DocumentUri.to_path textDocument.uri in
  begin match Hashtbl.find_opt states path with
  | None -> log (fun () -> "[textDocumentDidClose] closed document with no state")
  | Some { st } -> replace_state path st false
  end;
  consider_purge_invisible_tabs ();
  [] (* TODO handle properly *)

let textDocumentHover id params = 
  let Lsp.Types.HoverParams.{ textDocument; position } = params in
  let open Yojson.Safe.Util in
  match Hashtbl.find_opt states (DocumentUri.to_path textDocument.uri) with
  | None -> log (fun () -> "[textDocumentHover] ignoring event on non existing document"); Ok None (* FIXME handle error case properly *)
  | Some { st } ->
    match Dm.DocumentManager.hover st position with
    | Some contents -> Ok (Some (Hover.create ~contents:(`MarkupContent contents) ()))
    | _ -> Ok None (* FIXME handle error case properly *)

let textDocumentDefinition params =
  let Lsp.Types.DefinitionParams.{ textDocument; position } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path textDocument.uri) with
  | None -> log (fun () -> "[textDocumentDefinition] ignoring event on non existing document"); Ok None (* FIXME handle error case properly *)
  | Some { st } -> 
    match Dm.DocumentManager.jump_to_definition st position with
    | None -> log (fun () -> "[textDocumentDefinition] could not find symbol location"); Ok None (* FIXME handle error case properly *)
    | Some (range, uri) ->
      let uri = DocumentUri.of_path uri in
      let location = Location.create ~range:range ~uri:uri in
      Ok (Some (`Location [location]))


let progress_hook uri () =
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "ignoring non existent document")
  | Some { st } -> update_view uri st

let coqtopInterpretToPoint params =
  let Notification.Client.InterpretToPointParams.{ textDocument; position } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[interpretToPoint] ignoring event on non existent document"); []
  | Some { st; visible } ->
    let (st, events) = Dm.DocumentManager.interpret_to_position st position !check_mode ~point_interp_mode:!point_interp_mode
    in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    let sel_events = inject_dm_events (uri, events) in
    sel_events
 
let coqtopStepBackward params =
  let Notification.Client.StepBackwardParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[stepBackward] ignoring event on non existent document"); []
  | Some { st; visible } ->
      let (st, events) = Dm.DocumentManager.interpret_to_previous st !check_mode in
      replace_state (DocumentUri.to_path uri) st visible;
      inject_dm_events (uri,events)

let coqtopStepForward params =
  let Notification.Client.StepForwardParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[stepForward] ignoring event on non existent document"); []
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
  | None -> log (fun () -> "[textDocumentCompletion]ignoring event on non existent document"); Error( {message="Document does not exist"; code=None} ), []
  | Some { st } -> 
    let items = List.mapi make_CompletionItem (Dm.DocumentManager.get_completions st position) in
    return_completion ~isIncomplete:false ~items, []

let documentSymbol id params =
  let Lsp.Types.DocumentSymbolParams.{ textDocument = {uri}; partialResultToken; workDoneToken } = params in (*TODO: At some point we might get ssupport for partialResult and workDone*)
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[documentSymbol] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some tab -> log (fun () -> "[documentSymbol] getting symbols");
    if Dm.DocumentManager.is_parsing tab.st then
       (* Making use of the error codes: the ServerCancelled error code indicates 
       that the server is busy and the client should resend the request later.
       It doesn't seem to be working for documentSymbol at the moment. *)
      Error {code=(Some Jsonrpc.Response.Error.Code.ServerCancelled); message="Parsing not finished"} , []
    else
      let symbols = Dm.DocumentManager.get_document_symbols tab.st in
      Ok(Some (`DocumentSymbol symbols)), []

let coqtopResetCoq id params =
  let Request.Client.ResetParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[resetCoq] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st; visible } -> 
    let st, events = Dm.DocumentManager.reset st in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    Ok(()), (uri,events) |> inject_dm_events

let coqtopInterpretToEnd params =
  let Notification.Client.InterpretToEndParams.{ textDocument = { uri } } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[interpretToEnd] ignoring event on non existent document"); []
  | Some { st; visible } ->
    let (st, events) = Dm.DocumentManager.interpret_to_end st !check_mode in
    replace_state (DocumentUri.to_path uri) st visible;
    update_view uri st;
    inject_dm_events (uri,events)

let coqtopLocate id params = 
  let Request.Client.LocateParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[locate] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } ->
    Dm.DocumentManager.locate st position ~pattern, []

let coqtopPrint id params = 
  let Request.Client.PrintParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[print] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } -> Dm.DocumentManager.print st position ~pattern, []

let coqtopAbout id params =
  let Request.Client.AboutParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[about] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } -> Dm.DocumentManager.about st position ~pattern, []

let coqtopCheck id params =
  let Request.Client.CheckParams.{ textDocument = { uri }; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[check] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } -> Dm.DocumentManager.check st position ~pattern, []

let coqtopSearch id params =
  let Request.Client.SearchParams.{ textDocument = { uri }; id; position; pattern } = params in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[search] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } ->
    try
      let notifications = Dm.DocumentManager.search st ~id position pattern in
      Ok(()), inject_notifications notifications
    with e ->
      let e, info = Exninfo.capture e in
      let message = Pp.string_of_ppcmds @@ CErrors.iprint (e, info) in
      Error({message; code=None}), []

let sendDocumentState id params = 
  let Request.Client.DocumentStateParams.{ textDocument } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[documentState] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } -> let document = Dm.DocumentManager.Internal.string_of_state st in
    Ok Request.Client.DocumentStateResult.{ document }, []

let sendDocumentProofs id params = 
  let Request.Client.DocumentProofsParams.{ textDocument } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[documentProofs] ignoring event on non existent document"); Error({message="Document does not exist"; code=None}), []
  | Some { st } ->
    if Dm.DocumentManager.is_parsing st then
      Error {code=(Some Jsonrpc.Response.Error.Code.ServerCancelled); message="Parsing not finished"} , []
    else
      let proofs = Dm.DocumentManager.get_document_proofs st in
      Ok Request.Client.DocumentProofsResult.{ proofs }, []

let workspaceDidChangeConfiguration params = 
  let Lsp.Types.DidChangeConfigurationParams.{ settings } = params in
  let settings = Settings.t_of_yojson settings in
  do_configuration settings;
  match !check_mode with
  | Continuous -> run_documents ()
  | Manual -> reset_observe_ids (); ([] : events)

let handle_interrupt params =
  let Notification.Client.InterruptParams.{ textDocument } = params in
  let uri = textDocument.uri in
  match Hashtbl.find_opt states (DocumentUri.to_path uri) with
  | None -> log (fun () -> "[interrupt] ignoring event on non existent document"); []
  | Some { st } -> Dm.DocumentManager.cancel_ongoing_execution st; []

let dispatch_std_request : type a. Jsonrpc.Id.t -> a Lsp.Client_request.t -> (a, error) result * events =
  fun id req ->
  match req with
  | Initialize params ->
    do_initialize id params
  | Shutdown ->
    do_shutdown id ()
  | TextDocumentCompletion params ->
    textDocumentCompletion id params
  | TextDocumentDefinition params ->
    textDocumentDefinition params, []
  | TextDocumentHover params ->
    textDocumentHover id params, []
  | DocumentSymbol params ->
    documentSymbol id params
  | UnknownRequest _ | _  -> Error ({message="Received unknown request"; code=None}), []

let dispatch_request : type a. Jsonrpc.Id.t -> a Request.Client.t -> (a,error) result * events =
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
  | DocumentProofs params -> sendDocumentProofs id params

let dispatch_std_notification = 
  let open Lsp.Client_notification in function
  | TextDocumentDidOpen params -> log (fun () -> "Received notification: textDocument/didOpen");
    begin try textDocumentDidOpen params with
      exn -> let info = Exninfo.capture exn in
      let message = "Error while opening document. " ^ Pp.string_of_ppcmds @@ CErrors.iprint_no_report info in
      send_error_notification message; []
    end
  | TextDocumentDidChange params -> log (fun () -> "Received notification: textDocument/didChange");
    textDocumentDidChange params
  | TextDocumentDidClose params ->  log (fun () -> "Received notification: textDocument/didClose");
    textDocumentDidClose params
  | ChangeConfiguration params -> log (fun () -> "Received notification: workspace/didChangeConfiguration");
    workspaceDidChangeConfiguration params
  | Initialized -> []
  | Exit ->
    do_exit ()
  | UnknownNotification _ | _ -> log (fun () -> "Received unknown notification"); []

let dispatch_notification =
  let open Notification.Client in function
  | InterpretToPoint params -> log (fun () -> "Received notification: vscoq/interpretToPoint"); coqtopInterpretToPoint params 
  | InterpretToEnd params -> log (fun () -> "Received notification: vscoq/interpretToEnd"); coqtopInterpretToEnd params
  | StepBackward params -> log (fun () -> "Received notification: vscoq/stepBackward"); coqtopStepBackward params
  | StepForward params -> log (fun () -> "Received notification: vscoq/stepForward"); coqtopStepForward params
  | Interrupt params -> log (fun () -> "Received notification: vscoq/interrupt"); handle_interrupt params
  | Std notif -> dispatch_std_notification notif

let handle_lsp_event = function
  | Receive None -> [lsp]
  | Receive (Some rpc) ->
    lsp :: (* the event is recurrent *)
    begin try
      let json = Jsonrpc.Packet.yojson_of_t rpc in
      let msg = Yojson.Safe.pretty_to_string ~std:true json in
      log (fun () -> "recieved: " ^ msg);
      begin match rpc with
      | Request req ->
          log (fun () -> "ui request: " ^ req.method_);
          begin match Request.Client.t_of_jsonrpc req with
          | Error(e) -> log (fun () -> "Error decoding request: " ^ e); []
          | Ok(Pack r) ->
            let resp, events = dispatch_request req.id r in
            begin match resp with
            | Error {code; message} ->
              let code = Option.default Jsonrpc.Response.Error.Code.RequestFailed code in
              output_json @@ Jsonrpc.Response.(yojson_of_t @@ error req.id (Error.make ~code ~message ()))
            | Ok resp ->
              let resp = Request.Client.yojson_of_result r resp in
              output_json @@ Jsonrpc.Response.(yojson_of_t @@ ok req.id resp)
            end;
            events
          end
      | Notification notif ->
        begin match Notification.Client.of_jsonrpc notif with
        | Ok notif -> dispatch_notification notif
        | Error e -> log (fun () -> "error decoding notification: " ^ e); []
        end
      | Response resp ->
          log (fun () -> "got unknown response");
          []
      | Batch_response _ -> log (fun () -> "Unsupported batch response received"); []
      | Batch_call _ -> log (fun () -> "Unsupported batch call received"); []
      end
    with Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(exn,json) ->
      log (fun () -> "error parsing json: " ^ Yojson.Safe.pretty_to_string json);
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
      log (fun () -> "ignoring event on non-existing document");
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
