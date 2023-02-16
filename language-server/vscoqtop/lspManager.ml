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

let lsp_debug = CDebug.create ~name:"vscoq.lspManager" ()

let log msg = lsp_debug Pp.(fun () ->
  str @@ Format.asprintf "       [%d, %f] %s" (Unix.getpid ()) (Unix.gettimeofday ()) msg)

(*let string_field name obj = Yojson.Safe.to_string (List.assoc name obj)*)

type lsp_event = 
  | Request of Yojson.Safe.t option

type event =
 | LspManagerEvent of lsp_event
 | DocumentManagerEvent of string * Dm.DocumentManager.event
 | Notification of notification

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

let do_initialize ~id params =
  let open Yojson.Safe.Util in
  let capabilities = `Assoc [
    "textDocumentSync", `Int 2 (* Incremental *)
  ]
  in
  let result = Ok (`Assoc ["capabilities", capabilities]) in
  output_json Response.(yojson_of_t {id; result})

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
  let { Dm.DocumentManager.parsed; checked; checked_by_delegate; legacy_highlight } =
    Dm.DocumentManager.executed_ranges doc in
  let parsed = List.map Range.yojson_of_t parsed in
  let checked = List.map Range.yojson_of_t checked in
  (* let checked_by_delegate = List.map mk_range checked_by_delegate in *)
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

let textDocumentDidOpen params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let text = textDocument |> member "text" |> to_string in
  let vst, opts = get_init_state () in
  let st, events = Dm.DocumentManager.init vst ~opts ~uri ~text in
  let st = Dm.DocumentManager.validate_document st in
  let (st, events') = Dm.DocumentManager.interpret_to_end st in
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
  let (st, events) = Dm.DocumentManager.interpret_to_end st in
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

let progress_hook uri () =
  let st = Hashtbl.find states uri in
  update_view uri st

let coqtopInterpretToPoint ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let loc = params |> member "location" |> parse_loc in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_position st loc in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri, events)

let coqtopStepBackward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_previous st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

let coqtopStepForward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_next st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

let coqtopResetCoq ~id params =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.reset st in
  Hashtbl.replace states uri st;
  update_view uri st

let coqtopInterpretToEnd ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Safe.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_end st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

let inject_dm_event uri x : event Sel.event =
  Sel.map (fun e -> DocumentManagerEvent(uri,e)) x

let inject_notification x : event Sel.event =
  Sel.map (fun x -> Notification(x)) x

let inject_dm_events (uri,l) =
  List.map (inject_dm_event uri) l

let inject_notifications l =
  List.map inject_notification l

let coqtopUpdateProofView ~id params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_proof st loc with
  | None -> ()
  | Some proofview ->
    let result = Ok (mk_proofview proofview) in
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
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_proof st loc with
  | None -> ()
  | Some proofview ->
    let result = Ok (mk_proofview proofview) in
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

let vscoqConfiguration params = 
  let open Yojson.Safe.Util in 
  let delegation = params |> member "delegation" |> to_string in 
  let number_of_workers = params |> member "workers" |> to_int in
  let open Dm.ExecutionManager in
  let options =
    match delegation with
    | "None"     -> { delegation_mode = CheckProofsInMaster }
    | "Skip"     -> { delegation_mode = SkipProofs }
    | "Delegate" -> { delegation_mode = DelegateProofsToWorkers { number_of_workers } }
    | _ ->
      log @@ "Ignoring call to vscoqConfiguration with unknown delegation: " ^ delegation;
      default_options in
  Hashtbl.filter_map_inplace (fun _ st ->
    Some (Dm.DocumentManager.set_ExecutionManager_options st options)) states

let dispatch_method ~id method_name params : events =
  match method_name with
  | "initialize" -> do_initialize ~id params; []
  | "initialized" -> []
  | "shutdown" -> do_shutdown ~id params; []
  | "exit" -> do_exit ~id params
  | "textDocument/didOpen" -> textDocumentDidOpen params |> inject_dm_events
  | "textDocument/didChange" -> textDocumentDidChange params |> inject_dm_events
  | "textDocument/didSave" -> textDocumentDidSave params; []
  | "vscoq/configuration" -> vscoqConfiguration params; []
  | "vscoq/interpretToPoint" -> coqtopInterpretToPoint ~id params |> inject_dm_events
  | "vscoq/stepBackward" -> coqtopStepBackward ~id params |> inject_dm_events
  | "vscoq/stepForward" -> coqtopStepForward ~id params |> inject_dm_events
  | "vscoq/resetCoq" -> coqtopResetCoq ~id params; []
  | "vscoq/interpretToEnd" -> coqtopInterpretToEnd ~id params |> inject_dm_events
  | "vscoq/updateProofView" -> coqtopUpdateProofView ~id params; []
  | "vscoq/search" -> coqtopSearch ~id params |> inject_notifications
  | "vscoq/about" -> coqtopAbout ~id params; []
  | "vscoq/check" -> coqtopCheck ~id params; []
  | _ -> log @@ "Ignoring call to unknown method: " ^ method_name; []

let handle_lsp_event = function
  | Request None ->
      []
  | Request (Some req) ->
      let open Yojson.Safe.Util in
      let id = Option.default 0 (req |> member "id" |> to_int_option) in
      let method_name = req |> member "method" |> to_string in
      let params = req |> member "params" in
      log @@ "ui request: " ^ method_name;
      let more_events = dispatch_method ~id method_name params in
      more_events

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
        | Some st->
          Hashtbl.replace states uri st;
          update_view uri st
      end;
      inject_dm_events (uri, events)
    end
  | Notification notification ->
    output_notification notification; [inject_notification Dm.SearchQuery.query_feedback]

let pr_event = function
  | LspManagerEvent e -> pr_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    Pp.str @@ Format.asprintf "%a" Dm.DocumentManager.pp_event e
  | Notification _ -> Pp.str"notif"

let init injections =
  init_state := Some (Vernacstate.freeze_full_state ~marshallable:false, injections)


