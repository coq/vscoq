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
open Lsp.JsonRpc
open Lsp.LspEncode
open Lsp.LspData

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
  | Request of Yojson.Safe.t option

type event =
 | LspManagerEvent of lsp_event
 | DocumentManagerEvent of string * Dm.DocumentManager.event
 | Notification of notification
 | LogEvent of Dm.Log.event

type events = event Sel.event list

let lsp : event Sel.event =
  Sel.on_httpcle Unix.stdin (function
    | Ok buff ->
      begin
        log "UI req ready";
        try LspManagerEvent (Request (Some (Yojson.Safe.from_string (Bytes.to_string buff))))
        with exn ->
          log @@ "failed to decode json";
          LspManagerEvent (Request None)
      end
    | Error exn ->
        log @@ ("failed to read message: " ^ Printexc.to_string exn);
        (*this line is sacred*)
        exit(0))
  |> fst
  |> Sel.name "lsp"
  |> Sel.make_recurring
  |> Sel.set_priority Dm.PriorityManager.lsp_message

let output_json ?(trace=true) obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log @@ "sent: " ^ msg;
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

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
  let method_ = "workspace/configuration" in
  let mk_configuration_item section =
    ConfigurationItem.({ scopeUri = None; section = Some section })
  in
  let items = List.map mk_configuration_item ["vscoq"] in
  let params = ConfigurationParams.(yojson_of_t { items }) in
  output_json Request.(yojson_of_t { id; method_; params })
  
let do_initialize ~id params =
  let open Settings in
  let open Yojson.Safe.Util in
  let settings = params |> member "initializationOptions" |> Settings.t_of_yojson in
  do_configuration settings;
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
  let initialize_result = InitializeResult. {
    capabilities = capabilities; 
    serverInfo = server_info;
  } in
  let result = Ok (InitializeResult.yojson_of_t initialize_result) in
  output_json Response.(yojson_of_t {id; result});
  send_configuration_request ()

let do_shutdown ~id params =
  let open Yojson.Safe.Util in
  let result = Ok `Null in
  output_json Response.(yojson_of_t {id; result})

let do_exit ~id params =
  exit 0

let parse_loc json =
  let open Yojson.Safe.Util in
  let line = json |> member "line" |> to_int in
  let character = json |> member "character" |> to_int in
  Position.{ line ; character }

let publish_diagnostics uri doc =
  let diagnostics = List.map Diagnostic.yojson_of_t @@ Dm.DocumentManager.diagnostics doc in
  let params = `Assoc [
    "uri", `String uri;
    "diagnostics", `List diagnostics;
  ]
  in
  let method_ = "textDocument/publishDiagnostics" in
  output_json @@ Notification.(yojson_of_t { method_; params })

let send_highlights uri doc =
  let { Dm.DocumentManager.parsed; checked; legacy_highlight } =
    Dm.DocumentManager.executed_ranges doc in
  let parsed = List.map Range.yojson_of_t parsed in
  let checked = List.map Range.yojson_of_t checked in
  let legacy_highlight = List.map Range.yojson_of_t legacy_highlight in
  let params = `Assoc [
    "uri", `String uri;
    "parsedRange", `List parsed;
    "processingRange", `List checked;
    "processedRange", `List legacy_highlight;
  ]
  in
  let method_ = "vscoq/updateHighlights" in
  output_json @@ Notification.(yojson_of_t { method_; params })

let update_view uri st =
  send_highlights uri st;
  publish_diagnostics uri st

let send_proof_view ~id st loc = 
  let result = match Dm.DocumentManager.get_proof st loc with
  | None -> 
    Ok (`Null) 
  | Some proofview ->
    Ok (mk_proofview proofview) 
  in
  output_json @@ Response.(yojson_of_t { id; result })

let textDocumentDidOpen params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let text = textDocument |> member "text" |> to_string in
  let vst, opts = get_init_state () in
  let st, events = Dm.DocumentManager.init vst ~opts ~uri ~text in
  let st = Dm.DocumentManager.validate_document st in
  let (st, events') = 
    if !check_mode = Settings.Mode.Continuous then 
      Dm.DocumentManager.interpret_to_end st 
    else 
      (st, [])
  in
  Hashtbl.add states uri st;
  update_view uri st;
  uri, events@events'

let textDocumentDidChange params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let contentChanges = params |> member "contentChanges" |> to_list in
  let read_edit edit =
    let text = edit |> member "text" |> to_string in
    let range = Range.t_of_yojson (edit |> member "range") in
    range, text
  in
  let textEdits = List.map read_edit contentChanges in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.apply_text_edits st textEdits in
  let (st, events) = 
    if !check_mode = Settings.Mode.Continuous then 
      Dm.DocumentManager.interpret_to_end st 
    else 
      (st, [])
  in
  Hashtbl.replace states uri st;
  update_view uri st;
  uri, events

let textDocumentDidSave params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.validate_document st in
  Hashtbl.replace states uri st;
  update_view uri st

let textDocumentHover ~id params = 
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in 
  let st = Hashtbl.find states uri in 
  match Dm.DocumentManager.hover st loc with
  (* Response: result: Hover | null *)
  | None -> output_json @@ Response.(yojson_of_t { id; result = Ok (`Null) })
  | Some (Ok contents) ->
    let result = Ok (Hover.(yojson_of_t {contents})) in
    output_json @@ Response.(yojson_of_t { id; result })
  | _ -> ()

let progress_hook uri () =
  let st = Hashtbl.find states uri in
  update_view uri st

let coqtopInterpretToPoint ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in 
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_position st loc in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri, events)

let coqtopStepBackward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in 
  let uri = textDocument |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_previous st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

let coqtopStepForward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in 
  let uri = textDocument |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_next st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)
  
  let make_CompletionItem (label, typ, path) : CompletionItem.t = 
    {
      label;
      detail = Some typ;
      documentation = Some ("Path: " ^ path);
    } 

  let textDocumentCompletion ~id params =
    let open Yojson.Safe.Util in
    let textDocument = params |> member "textDocument" in
    let uri = textDocument |> member "uri" |> to_string in
    let loc = params |> member "position" |> parse_loc in
    let st = Hashtbl.find states uri in
    let completionItems = Dm.CompletionSuggester.get_completion_items ~id params st loc in
    let items = List.map make_CompletionItem completionItems in
    let result = Ok (CompletionList.yojson_of_t {isIncomplete = false; items = items;}) in
    output_json @@ Response.(yojson_of_t { id; result })

let coqtopResetCoq ~id params =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.reset st in
  Hashtbl.replace states uri st;
  update_view uri st

let coqtopInterpretToEnd ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in 
  let uri = textDocument |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_end st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

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

let coqtopUpdateProofView ~id params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> to_option parse_loc in
  let st = Hashtbl.find states uri in
  send_proof_view ~id st loc

let coqtopLocate ~id params = 
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let pattern = params |> member "pattern" |> to_string in 
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.locate st loc ~pattern with
  | Error _ -> ()
  | Ok str ->
    let result = Ok (`String str) in
    output_json @@ Response.(yojson_of_t { id; result })

let coqtopPrint ~id params = 
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let pattern = params |> member "pattern" |> to_string in 
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.print st loc ~pattern with
  | Error _ -> ()
  | Ok str ->
    let result = Ok (`String str) in
    output_json @@ Response.(yojson_of_t { id; result })

let coqtopAbout ~id params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in(* 
  let goalIndex = params |> member "goalIndex" in *)
  let pattern = params |> member "pattern" |> to_string in 
  let st = Hashtbl.find states uri in
  let goal = None in (*TODO*)
  match Dm.DocumentManager.about st loc ~goal ~pattern with
  | Error _ -> ()
  | Ok str ->
    let result = Ok (`String str) in
    output_json @@ Response.(yojson_of_t { id; result })

let coqtopCheck ~id params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let pattern = params |> member "pattern" |> to_string in 
  let st = Hashtbl.find states uri in
  let goal = None in (*TODO*)
  match Dm.DocumentManager.check st loc ~goal ~pattern with
  | Error _ -> ()
  | Ok str ->
    let result = Ok (`String str) in
    output_json @@ Response.(yojson_of_t { id; result })

  let coqtopSearch ~id params =
    let open Yojson.Safe.Util in
    let textDocument = params |> member "textDocument" in
    let uri = textDocument |> member "uri" |> to_string in
    let loc = params |> member "position" |> parse_loc in
    let pattern = params |> member "pattern" |> to_string in
    let search_id = params |> member "id" |> to_string in
    let st = Hashtbl.find states uri in
    try
      let notifications = Dm.DocumentManager.search st ~id:search_id loc pattern in
      let result = Ok `Null in
      output_json @@ Response.(yojson_of_t {id; result}); notifications
    with e ->
      let e, info = Exninfo.capture e in
      let code = Lsp.LspData.Error.requestFailed in
      let message = Pp.string_of_ppcmds @@ CErrors.iprint (e, info) in
      let error = Response.Error.{ code; message } in
      output_json @@ Response.(yojson_of_t { id; result = Error error}); []

  let coqtopSearchResult ~id name statement =
    let method_ = "vscoq/searchResult" in
    let params = `Assoc [ "id", `String id; "name", `String name; "statement", `String statement ] in
    output_json @@ Notification.(yojson_of_t {method_; params})

let workspaceDidChangeConfiguration params = 
  let open Yojson.Safe.Util in 
  let settings = params |> member "settings" |> Settings.t_of_yojson in
  do_configuration settings


let dispatch_method ~id method_name params : events =
  log ("dispatching: "^method_name);
  match method_name with
  | "initialize" -> do_initialize ~id params; []
  | "initialized" ->
    log "---------------- initialized --------------";
    Dm.Log.lsp_initialization_done () |> inject_debug_events
  | "shutdown" -> do_shutdown ~id params; []
  | "exit" -> do_exit ~id params
  | "workspace/didChangeConfiguration" -> workspaceDidChangeConfiguration params; []
  | "textDocument/didOpen" -> textDocumentDidOpen params |> inject_dm_events
  | "textDocument/didChange" -> textDocumentDidChange params |> inject_dm_events
  | "textDocument/didSave" -> textDocumentDidSave params; []
  | "textDocument/completion" -> textDocumentCompletion ~id params; []
  | "textDocument/hover" -> textDocumentHover ~id params; []
  | "vscoq/interpretToPoint" -> coqtopInterpretToPoint ~id params |> inject_dm_events
  | "vscoq/stepBackward" -> coqtopStepBackward ~id params |> inject_dm_events
  | "vscoq/stepForward" -> coqtopStepForward ~id params |> inject_dm_events
  | "vscoq/resetCoq" -> coqtopResetCoq ~id params; []
  | "vscoq/interpretToEnd" -> coqtopInterpretToEnd ~id params |> inject_dm_events
  | "vscoq/updateProofView" -> coqtopUpdateProofView ~id params; []
  | "vscoq/search" -> coqtopSearch ~id params |> inject_notifications
  | "vscoq/about" -> coqtopAbout ~id params; []
  | "vscoq/check" -> coqtopCheck ~id params; []
  | "vscoq/locate" -> coqtopLocate ~id params; []
  | "vscoq/print" -> coqtopPrint ~id params; []
  | _ -> log @@ "Ignoring call to unknown method: " ^ method_name; []

let handle_lsp_event = function
  | Request None ->
      []
  | Request (Some req) ->
      let open Yojson.Safe.Util in
      let id = Option.default 0 (req |> member "id" |> to_int_option) in
      let method_name = req |> member "method" |> to_string_option in
      match method_name with
      | Some method_ ->
        let params = req |> member "params" in
        log @@ "ui request: " ^ method_;
        let more_events = dispatch_method ~id method_ params in
        more_events
      | None -> 
        log @@ "got response: " ^ Yojson.Safe.pretty_to_string req;
        if id = conf_request_id then begin
          let result = req |> member "result" |> convert_each Settings.t_of_yojson in
          let _error = req |> member "error" in
          match result with
          | [settings] -> do_configuration settings; []
          | _ -> log "invalid settings object."; []
        end
      else begin 
        log "unknown response.";
        []
      end

let pr_lsp_event = function
  | Request req ->
    Pp.str "Request"

let output_notification = function
| QueryResultNotification params ->
  let method_ = "vscoq/searchResult" in
  output_json @@ Notification.(yojson_of_t { method_; params = yojson_of_query_result params })

let handle_event = function
  | LspManagerEvent e -> handle_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    begin match Hashtbl.find_opt states uri with
    | None ->
      log @@ "ignoring event on non-existing document";
      []
    | Some st ->
      let (ost, events) = Dm.DocumentManager.handle_event e st in
      begin match ost with
        | None -> ()
        | Some st ->
          Hashtbl.replace states uri st;
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


