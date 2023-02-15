(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

open Printer
open Lsp.LspEncode
open Lsp.LspData

module TraceValue = struct
  type t =
    | Off
    | Messages
    | Verbose

  let of_string = function
    | "messages" -> Messages
    | "verbose" -> Verbose
    | "off" -> Off
    | _ -> raise (Invalid_argument "TraceValue.parse")

  let to_string = function
    | Off -> "off"
    | Messages -> "messages"
    | Verbose -> "verbose"
end

let trace_value = ref TraceValue.Off

module CompactedDecl = Context.Compacted.Declaration

let init_state : (Vernacstate.t * Coqargs.injection_command list) option ref = ref None
let get_init_state () =
  match !init_state with
  | Some st -> st
  | None -> CErrors.anomaly Pp.(str "Initial state not available")

let states : (string, Dm.DocumentManager.state) Hashtbl.t = Hashtbl.create 39

let lsp_debug = CDebug.create ~name:"vscoq.lspManager" ()

let log msg = lsp_debug Pp.(fun () -> 
  str @@ Format.asprintf "       [%d] %s" (Unix.getpid ()) msg)

(*let string_field name obj = Yojson.Basic.to_string (List.assoc name obj)*)

type lsp_event = 
  | Request of Yojson.Basic.t option

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
        try LspManagerEvent (Request (Some (Yojson.Basic.from_string (Bytes.to_string buff))))
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

let logTrace ~message ~extra =
  let event = "$/logTrace" in
  let params =
      match (!trace_value, extra) with
      | Verbose, Some extra ->
        `Assoc [ ("message", `String message); ("verbose", `String extra) ]
      | _, _ -> `Assoc [ ("message", `String message) ]
  in
  mk_notification ~event ~params 

let output_json ?(trace=true) obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log @@ "sent: " ^ msg;
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

let logMessage ~lvl ~message =
  let event = "window/logMessage" in
  let params = `Assoc [ "type", `String lvl; "message", `String message ] in
  output_json @@ mk_notification ~event ~params

let do_initialize ~id params =
  let open Yojson.Basic.Util in
  let trace = params |> member "trace" |> to_string in
  let capabilities = `Assoc [
    "textDocumentSync", `Int 2 (* Incremental *);
    "completionProvider", `Assoc [
      "completionItem", `Assoc [
        "labelDetailsSupport", `Bool false;
      ]
    ];
    "declarationProvider", `Bool true;
  ]
  in
  let result = `Assoc ["capabilities", capabilities] in
  trace_value := TraceValue.of_string trace;
  output_json @@ mk_response ~id ~result

let do_shutdown ~id params =
  let open Yojson.Basic.Util in
  let result = `Null in
  output_json @@ mk_response ~id ~result

let do_exit ~id params =
  exit 0

let parse_loc json =
  let open Yojson.Basic.Util in
  let line = json |> member "line" |> to_int in
  let char = json |> member "character" |> to_int in
  Position.{ line ; char }

let make_loc Position.{ line; char }  = 
  `Assoc [
    "line", `Int line;
    "character", `Int char;
  ]

let make_range Range.{ start; stop } =
  `Assoc [
    "start", make_loc start;
    "end", make_loc stop;
  ]

let publish_diagnostics uri doc =
  output_json @@ mk_diagnostics uri @@ Dm.DocumentManager.diagnostics doc

let send_highlights uri doc =
  let { Dm.DocumentManager.parsed; checked; checked_by_delegate; legacy_highlight } =
    Dm.DocumentManager.executed_ranges doc in
  let parsed = List.map mk_range parsed in
  let checked = List.map mk_range checked in
  (* let checked_by_delegate = List.map mk_range checked_by_delegate in *)
  let legacy_highlight = List.map mk_range legacy_highlight in
    let params = `Assoc [
    "uri", `String uri;
    "parsedRange", `List parsed;
    "processingRange", `List checked;
    "processedRange", `List legacy_highlight;
  ]
  in
  output_json @@ mk_notification ~event:"vscoq/updateHighlights" ~params


let update_view uri st =
  send_highlights uri st;
  publish_diagnostics uri st

let textDocumentDidOpen params =
  let open Yojson.Basic.Util in
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
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let contentChanges = params |> member "contentChanges" |> to_list in
  let read_edit edit =
    let text = edit |> member "text" |> to_string in
    let range = edit |> member "range" in
    let start = range |> member "start" |> parse_loc in
    let stop = range |> member "end" |> parse_loc in
    Range.{ start; stop }, text
  in
  let textEdits = List.map read_edit contentChanges in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.apply_text_edits st textEdits in
  let (st, events) = Dm.DocumentManager.interpret_to_end st in
  Hashtbl.replace states uri st;
  update_view uri st;
  uri, events

let textDocumentDidSave params =
  let open Yojson.Basic.Util in
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
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let loc = params |> member "location" |> parse_loc in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_position st loc in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri, events)

let coqtopStepBackward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_previous st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

let coqtopStepForward ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let (st, events) = Dm.DocumentManager.interpret_to_next st in
  Hashtbl.replace states uri st;
  update_view uri st;
  (uri,events)

  let make_label (item : Dm.CompletionItem.completion_item) = 
    let (label, typ, path) = Dm.CompletionItem.pp_completion_item item in
    `Assoc [
      "label", `String label;
      "detail", `String typ;
      "documentation", `String ("Path: " ^ path)
    ]
  
  let completionDebugInfo labels = 
    `Assoc [
        "completionItems", `List (List.map make_label labels)
      ]
  
  let mk_hyp sigma d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right Environ.push_named d' env in
    let ids, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) -> ids, typ
    | CompactedDecl.LocalDef (ids,c,typ) -> ids, typ
    in
    let ids' = List.map (fun id -> `String (Names.Id.to_string id.Context.binder_name)) ids in
    let typ' = pr_ltype_env env sigma typ in
      let hyps = ids' |> List.map (fun id -> `Assoc [
        "label", id;
        "detail", `String (Pp.string_of_ppcmds typ')
      ]) in
      (env', hyps @ l)

  let mk_hyps sigma goal =
    let evi = Evd.find sigma goal in
    let env = Evd.evar_filtered_env (Global.env ()) evi in
    let min_env = Environ.reset_context env in
    let (_env, hyps) =
      Context.Compacted.fold (mk_hyp sigma)
        (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
    hyps

  let textDocumentCompletion ~id params =
    let open Yojson.Basic.Util in
    let textDocument = params |> member "textDocument" in
    let uri = textDocument |> member "uri" |> to_string in
    let loc = params |> member "position" |> parse_loc in
    let st = Hashtbl.find states uri in
    let hypotheses =
      Dm.DocumentManager.get_proof st loc
      |> Option.map (fun Proof.{ goals; sigma; _ } -> Option.cata (mk_hyps sigma) [] (List.nth_opt goals 0)) in
    let lemmas = Dm.DocumentManager.get_lemmas st loc |> Option.map (List.map make_label) in
    let result = `List ([hypotheses; lemmas]
      |> List.map (Option.default [])
      |> List.flatten) in
      output_json @@ mk_response ~id ~result

let textDocumentDeclaration ~id params =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_declaration_location st loc with
  | None -> 
    output_json @@ mk_error_response ~id ~code:(-32603) ~message:"Failed in finding declaration"
  | Some (path, rangeOpt) ->
    let v_file = Str.replace_first (Str.regexp {|\.vo$|}) ".v" path in
    let range = Option.default ({ start = { line = 0; char = 0 }; stop = { line = 0; char = 0 } } : Range.t) rangeOpt in
    if Sys.file_exists v_file then
      let result = `Assoc [
        "uri", `String v_file;
        "range", make_range range
      ] in
      output_json @@ mk_response ~id ~result
    else 
      output_json @@ mk_error_response ~id ~code:(-32603) ~message:("Unable to find .v file at expected location: " ^ v_file)

let coqtopResetCoq ~id params =
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.reset st in
  Hashtbl.replace states uri st;
  update_view uri st

let coqtopInterpretToEnd ~id params : (string * Dm.DocumentManager.events) =
  let open Yojson.Basic.Util in
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
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_proof st loc with
  | None -> ()
  | Some proofview ->
    let result = mk_proofview proofview in
    output_json @@ mk_response ~id ~result 

let coqtopAbout ~id params =
  let open Yojson.Basic.Util in
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
    output_json @@ mk_response ~id ~result:(`String str)

let coqtopCheck ~id params =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_proof st loc with
  | None -> ()
  | Some proofview ->
    let result = mk_proofview proofview in
    output_json @@ mk_response ~id ~result 

  let coqtopSearch ~id params =
    let open Yojson.Basic.Util in
    let textDocument = params |> member "textDocument" in
    let uri = textDocument |> member "uri" |> to_string in
    let loc = params |> member "position" |> parse_loc in
    let pattern = params |> member "pattern" |> to_string in
    let search_id = params |> member "id" |> to_string in
    let st = Hashtbl.find states uri in
    try
      let notifications = Dm.DocumentManager.search st ~id:search_id loc pattern in
      let result = `Null in
      output_json @@ mk_response ~id ~result; notifications
    with e ->
      let e, info = Exninfo.capture e in
      let code = Lsp.LspData.Error.requestFailed in
      let message = Pp.string_of_ppcmds @@ CErrors.iprint (e, info) in
      output_json @@ mk_error_response ~id ~code ~message; []

  let coqtopSearchResult ~id name statement =
    let event = "vscoq/searchResult" in
    let params = `Assoc [ "id", `String id; "name", `String name; "statement", `String statement ] in
    output_json @@ mk_notification ~event ~params

let dispatch_method ~id method_name params : events =
  match method_name with
  | "initialize" -> do_initialize ~id params; []
  | "initialized" -> []
  | "shutdown" -> do_shutdown ~id params; []
  | "exit" -> do_exit ~id params
  | "textDocument/didOpen" -> textDocumentDidOpen params |> inject_dm_events
  | "textDocument/didChange" -> textDocumentDidChange params |> inject_dm_events
  | "textDocument/didSave" -> textDocumentDidSave params; []
  | "textDocument/completion" -> textDocumentCompletion ~id params; []
  | "textDocument/declaration" -> textDocumentDeclaration ~id params; []
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
      let open Yojson.Basic.Util in
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
  output_json @@ mk_notification ~event:"vscoq/searchResult" ~params:(yojson_of_query_result params)

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
    Dm.DocumentManager.pr_event e
  | Notification _ -> Pp.str"notif"

let init injections =
  init_state := Some (Vernacstate.freeze_full_state ~marshallable:false, injections)


