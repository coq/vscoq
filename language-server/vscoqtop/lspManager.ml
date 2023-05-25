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
open Lsp
open LspEncode
open LspData
open ExtProtocol

module CompactedDecl = Context.Compacted.Declaration

let init_state : (Vernacstate.t * Coqargs.injection_command list) option ref = ref None
let get_init_state () =
  match !init_state with
  | Some st -> st
  | None -> CErrors.anomaly Pp.(str "Initial state not available")

let states : (string, Dm.DocumentManager.state) Hashtbl.t = Hashtbl.create 39

let check_mode = ref Settings.Mode.Continuous

let Dm.Types.Log log = Dm.Log.mk_log "lspManager"

let conf_request_id = 3456736879

let server_info = ServerInfo.{
  name = "vscoq-language-server";
  version = "2.0.0";
} 

type lsp_event = 
  | Receive of JsonRpc.t option
  | Send of JsonRpc.t

type event =
 | LspManagerEvent of lsp_event
 | DocumentManagerEvent of Uri.t * Dm.DocumentManager.event
 | Notification of notification
 | LogEvent of Dm.Log.event

type events = event Sel.event list

let lsp : event Sel.event =
  Sel.on_httpcle Unix.stdin (function
    | Ok buff ->
      begin
        log "UI req ready";
        try LspManagerEvent (Receive (Some (JsonRpc.t_of_yojson (Yojson.Safe.from_string (Bytes.to_string buff)))))
        with exn ->
          log @@ "failed to decode json";
          LspManagerEvent (Receive None)
      end
    | Error exn ->
        log @@ ("failed to read message: " ^ Printexc.to_string exn);
        (* do not remove this line otherwise the server stays running in some scenarios *)
        exit 0)
  |> fst
  |> Sel.name "lsp"
  |> Sel.make_recurring
  |> Sel.set_priority Dm.PriorityManager.lsp_message

let output_json obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log @@ "sent: " ^ msg;
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

let output_jsonrpc jsonrpc =
  output_json @@ JsonRpc.yojson_of_t jsonrpc

let inject_dm_event uri x : event Sel.event =
  Sel.map (fun e -> DocumentManagerEvent(uri,e)) x

let inject_notification x : event Sel.event =
  Sel.map (fun x -> Notification(x)) x

let inject_debug_event x : event Sel.event =
  Sel.map (fun x -> LogEvent x) x

let inject_dm_events (uri,l) =
  List.map (inject_dm_event uri) l

let inject_notifications l =
  List.map inject_notification l

let inject_debug_events l =
  List.map inject_debug_event l

let do_configuration settings = 
  let open Settings in
  let open Dm.ExecutionManager in
  let options =
    match settings.proof.delegation with
    | None     -> { delegation_mode = CheckProofsInMaster }
    | Skip     -> { delegation_mode = SkipProofs }
    | Delegate -> { delegation_mode = DelegateProofsToWorkers { number_of_workers = Option.get settings.proof.workers } }
  in
  Dm.ExecutionManager.set_options options;
  check_mode := settings.proof.mode

let send_configuration_request () =
  let id = conf_request_id in
  let mk_configuration_item section =
    ConfigurationItem.({ scopeUri = None; section = Some section })
  in
  let items = List.map mk_configuration_item ["vscoq"] in
  let req = Request.Server.(jsonrpc_of_t @@ Configuration (id, { items })) in
  Send (Request req)

let do_initialize ~id params =
  let Request.Client.InitializeParams.{ initializationOptions } = params in
  do_configuration initializationOptions;
  let capabilities = ServerCapabilities.{
    textDocumentSync = Incremental;
    completionProvider = { 
      resolveProvider = Some false; 
      triggerCharacters = None; 
      allCommitCharacters = None; 
      completionItem = None 
    };
    hoverProvider = true;
  } in
  let initialize_result = Request.Client.InitializeResult.{
    capabilities = capabilities; 
    serverInfo = server_info;
  } in
  log "---------------- initialized --------------";
  let debug_events = Dm.Log.lsp_initialization_done () |> inject_debug_events in
  Ok initialize_result, debug_events@[Sel.now @@ LspManagerEvent (send_configuration_request ())]

let do_shutdown ~id params =
  Ok(()), []

let do_exit () =
  exit 0

let parse_loc json =
  let open Yojson.Safe.Util in
  let line = json |> member "line" |> to_int in
  let character = json |> member "character" |> to_int in
  Position.{ line ; character }

let publish_diagnostics uri doc =
  let diagnostics = Dm.DocumentManager.diagnostics doc in
  let notification = Protocol.Notification.Server.PublishDiagnostics {
    uri;
    diagnostics
  }
  in
  output_jsonrpc @@ Notification Protocol.Notification.Server.(jsonrpc_of_t notification)

let send_highlights uri doc =
  let { Dm.DocumentManager.parsed; checked; checked_by_delegate; legacy_highlight } =
    Dm.DocumentManager.executed_ranges doc in
  let notification = Notification.Server.UpdateHighlights {
    uri;
    parsedRange = parsed;
    processingRange = checked;
    processedRange = legacy_highlight;
  }
  in
  output_jsonrpc @@ Notification Notification.Server.(jsonrpc_of_t notification)

let update_view uri st =
  send_highlights uri st;
  publish_diagnostics uri st

let textDocumentDidOpen params =
  let Notification.Client.DidOpenTextDocumentParams.{ textDocument = { uri; text } } = params in
  let vst, opts = get_init_state () in
  let st, events = Dm.DocumentManager.init vst ~opts uri ~text in
  let st = Dm.DocumentManager.validate_document st in
  let (st, events') = 
    if !check_mode = Settings.Mode.Continuous then 
      Dm.DocumentManager.interpret_to_end st 
    else 
      (st, [])
  in
  Hashtbl.add states (Uri.path uri) st;
  update_view uri st;
  inject_dm_events (uri, events@events')

let textDocumentDidChange params =
  let Notification.Client.DidChangeTextDocumentParams.{ textDocument; contentChanges } = params in
  let uri = textDocument.uri in
  let st = Hashtbl.find states (Uri.path uri) in
  let mk_text_edit TextDocumentContentChangeEvent.{ range; text } =
    Option.get range, text
  in
  let text_edits = List.map mk_text_edit contentChanges in
  let st = Dm.DocumentManager.apply_text_edits st text_edits in
  let (st, events) = 
    if !check_mode = Settings.Mode.Continuous then 
      Dm.DocumentManager.interpret_to_end st 
    else 
      (st, [])
  in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  inject_dm_events (uri, events)

let textDocumentDidSave params =
  let Notification.Client.DidChangeTextDocumentParams.{ textDocument } = params in
  let uri = textDocument.uri in
  let st = Hashtbl.find states (Uri.path uri) in
  let st = Dm.DocumentManager.validate_document st in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st

let textDocumentDidClose params =
  [] (* TODO handle properly *)

let textDocumentHover ~id params = 
  let Request.Client.HoverParams.{ textDocument; position } = params in
  let open Yojson.Safe.Util in
  let st = Hashtbl.find states (Uri.path textDocument.uri) in 
  match Dm.DocumentManager.hover st position with
  | Some (Ok contents) -> Ok (Some (Request.Client.HoverResult.{ contents }))
  | _ -> Ok None (* FIXME handle error case properly *)

let progress_hook uri () =
  let st = Hashtbl.find states (Uri.path uri) in
  update_view uri st

let coqtopInterpretToPoint ~id params =
  let Request.Client.InterpretToPointParams.{ textDocument; position } = params in
  let uri = textDocument.uri in
  let st = Hashtbl.find states (Uri.path uri) in
  let (st, events) = Dm.DocumentManager.interpret_to_position st position in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  Ok(()), inject_dm_events (uri, events)

let coqtopStepBackward ~id params =
  let Request.Client.StepBackwardParams.{ textDocument = { uri } } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let (st, events) = Dm.DocumentManager.interpret_to_previous st in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  Ok(()), inject_dm_events (uri,events)

let coqtopStepForward ~id params =
  let Request.Client.StepForwardParams.{ textDocument = { uri } } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let (st, events) = Dm.DocumentManager.interpret_to_next st in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  Ok(()), inject_dm_events (uri,events)
  
 let make_CompletionItem (label, typ, path) : CompletionItem.t = 
   {
     label;
     detail = Some typ;
     documentation = Some ("Path: " ^ path);
   } 

 let textDocumentCompletion ~id params =
   let Request.Client.CompletionParams.{ textDocument = { uri }; position } = params in
   let st = Hashtbl.find states (Uri.path uri) in
   let completionItems = Dm.CompletionSuggester.get_completion_items ~id params st position in
   let items = List.map make_CompletionItem completionItems in
   Ok Request.Client.CompletionResult.{isIncomplete = false; items = items;}, []

let coqtopResetCoq ~id params =
  let Request.Client.ResetParams.{ uri } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let st = Dm.DocumentManager.reset st in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  Ok(()), []

let coqtopInterpretToEnd ~id params =
  let Request.Client.InterpretToEndParams.{ textDocument = { uri } } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let (st, events) = Dm.DocumentManager.interpret_to_end st in
  Hashtbl.replace states (Uri.path uri) st;
  update_view uri st;
  Ok(()), inject_dm_events (uri,events)

let coqtopUpdateProofView ~id params =
  let Request.Client.UpdateProofViewParams.{ textDocument = { uri }; position } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  Ok(Dm.DocumentManager.get_proof st (Some position)), []

let coqtopLocate ~id params = 
  let Request.Client.LocateParams.{ textDocument = { uri }; position; pattern } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  Dm.DocumentManager.locate st position ~pattern, []

let coqtopPrint ~id params = 
  let Request.Client.PrintParams.{ textDocument = { uri }; position; pattern } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  Dm.DocumentManager.print st position ~pattern, []

let coqtopAbout ~id params =
  let Request.Client.AboutParams.{ textDocument = { uri }; position; pattern } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let goal = None in (*TODO*)
  Dm.DocumentManager.about st position ~goal ~pattern, []

let coqtopCheck ~id params =
  let Request.Client.CheckParams.{ textDocument = { uri }; position; pattern } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  let goal = None in (*TODO*)
  Dm.DocumentManager.check st position ~goal ~pattern, []

let coqtopSearch ~id params =
  let Request.Client.SearchParams.{ textDocument = { uri }; id; position; pattern } = params in
  let st = Hashtbl.find states (Uri.path uri) in
  try
    let notifications = Dm.DocumentManager.search st ~id position pattern in
    Ok(()), inject_notifications notifications
  with e ->
    let e, info = Exninfo.capture e in
    let message = Pp.string_of_ppcmds @@ CErrors.iprint (e, info) in
    Error(message), []

let workspaceDidChangeConfiguration params = 
  let Protocol.Notification.Client.DidChangeConfigurationParams.{ settings } = params in
  let settings = Settings.t_of_yojson settings in
  do_configuration settings;
  []

let dispatch_request : type a. id:int -> a Protocol.Request.Client.params -> (a,string) result * events =
  fun ~id req ->
  match req with
  | Initialize params ->
    do_initialize ~id params
  | Shutdown ->
    do_shutdown ~id ()
  | Completion params ->
    textDocumentCompletion ~id params
  | Hover params ->
    textDocumentHover ~id params, []
  | UnknownRequest -> Ok(()), []

let dispatch_ext_request : type a. id:int -> a Request.Client.params -> (a,string) result * events =
  fun ~id req ->
  match req with
  | InterpretToPoint params -> coqtopInterpretToPoint ~id params
  | InterpretToEnd params -> coqtopInterpretToEnd ~id params
  | StepBackward params -> coqtopStepBackward ~id params
  | StepForward params -> coqtopStepForward ~id params
  | UpdateProofView params -> coqtopUpdateProofView ~id params
  | Reset params -> coqtopResetCoq ~id params
  | About params -> coqtopAbout ~id params
  | Check params -> coqtopCheck ~id params
  | Locate params -> coqtopLocate ~id params
  | Print params -> coqtopPrint ~id params
  | Search params -> coqtopSearch ~id params

let dispatch_notification =
  let open Notification.Client in function
  | DidOpenTextDocument params ->
    textDocumentDidOpen params
  | DidChangeTextDocument params ->
    textDocumentDidChange params
  | DidCloseTextDocument params ->
    textDocumentDidClose params
  | DidChangeConfiguration params ->
    workspaceDidChangeConfiguration params
  | Initialized -> []
  | Exit ->
    do_exit ()
  | UnknownNotification -> []

let dispatch = Request.Client.{ dispatch_std = dispatch_request; dispatch_ext = dispatch_ext_request }

let handle_lsp_event = function
  | Receive None ->
      []
  | Receive (Some rpc) ->
    begin try
      begin match rpc with
      | Request req ->
          log @@ "ui request: " ^ req.method_;
          let resp, events = Request.Client.yojson_of_result req dispatch in
          output_json resp;
          events
      | Notification notif ->
        dispatch_notification @@ Notification.Client.t_of_jsonrpc notif
      | Response resp ->
          log @@ "got unknown response";
          []
      end
    with Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(exn,json) ->
      log @@ "error parsing json: " ^ Yojson.Safe.pretty_to_string json;
      []
    end
  | Send jsonrpc ->
    output_json (JsonRpc.yojson_of_t jsonrpc); []

let pr_lsp_event = function
  | Receive jsonrpc ->
    Pp.str "Request"
  | Send jsonrpc ->
    Pp.str "Send"

let output_notification = function
| QueryResultNotification params ->
  output_jsonrpc @@ Notification Notification.Server.(jsonrpc_of_t @@ SearchResult params)

let handle_event = function
  | LspManagerEvent e -> handle_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    begin match Hashtbl.find_opt states (Uri.path uri) with
    | None ->
      log @@ "ignoring event on non-existing document";
      []
    | Some st ->
      let (ost, events) = Dm.DocumentManager.handle_event e st in
      begin match ost with
        | None -> ()
        | Some st ->
          Hashtbl.replace states (Uri.path uri) st;
          update_view uri st
      end;
      inject_dm_events (uri, events)
    end
  | Notification notification ->
    output_notification notification; [inject_notification Dm.SearchQuery.query_feedback]
  | LogEvent e ->
    Dm.Log.handle_event e; []

let pr_event = function
  | LspManagerEvent e -> pr_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    Pp.str @@ Format.asprintf "%a" Dm.DocumentManager.pp_event e
  | Notification _ -> Pp.str"notif"
  | LogEvent _ -> Pp.str"debug"

let init injections =
  init_state := Some (Vernacstate.freeze_full_state ~marshallable:false, injections);
  [lsp]
