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
        LspManagerEvent (Request None))

let output_json obj =
  let msg  = Yojson.Basic.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  (* log @@ "sent: " ^ msg; *)
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

let mk_notification ~event ~params = `Assoc ["jsonrpc", `String "2.0"; "method", `String event; "params", params]
let mk_response ~id ~result = `Assoc ["jsonrpc", `String "2.0"; "id", `Int id; "result", result]

let do_initialize ~id =
  let capabilities = `Assoc [
    "textDocumentSync", `Int 2 (* Incremental *)
  ]
  in
  let result = `Assoc ["capabilities", capabilities] in
  output_json @@ mk_response ~id ~result

let parse_loc json =
  let open Yojson.Basic.Util in
  let line = json |> member "line" |> to_int in
  let char = json |> member "character" |> to_int in
  Dm.Types.Position.{ line ; char }

let mk_loc Dm.Types.Position.{ line; char } =
  `Assoc [
    "line", `Int line;
    "character", `Int char;
  ]

let mk_range Dm.Types.Range.{ start; stop } =
  `Assoc [
    "start", mk_loc start;
    "end", mk_loc stop;
  ]

let publish_diagnostics uri doc =
  let mk_severity lvl =
    let open Feedback in
    `Int (match lvl with
    | Error -> 1
    | Warning -> 2
    | Notice -> 3
    | Info -> 3
    | Debug -> 3
    )
  in
  let mk_diagnostic d =
    let open Dm.DocumentManager in
    `Assoc [
      "range", mk_range d.range;
      "severity", mk_severity d.severity;
      "message", `String d.message;
    ]
  in
  let diagnostics = List.map mk_diagnostic @@ Dm.DocumentManager.diagnostics doc in
  let params = `Assoc [
    "uri", `String uri;
    "diagnostics", `List diagnostics;
  ]
  in
  output_json @@ mk_notification ~event:"textDocument/publishDiagnostics" ~params

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

let mk_goal sigma g =
  let evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let min_env = Environ.reset_context env in
  let id = Evar.repr g in
  let ccl =
    pr_letype_env ~goal_concl_style:true env sigma (Evd.evar_concl evi)
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right Environ.push_named d' env in
    let ids, body, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, None, typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
      ids, Some c, typ
    in
  let ids = List.map (fun id -> `String (Names.Id.to_string id.Context.binder_name)) ids in
  let typ = pr_ltype_env env sigma typ in
    let hyp = `Assoc ([
      "identifiers", `List ids;
      "type", `String (Pp.string_of_ppcmds typ);
      "diff", `String "None";
    ] @ Option.cata (fun body -> ["body", `String (Pp.string_of_ppcmds @@ pr_lconstr_env ~inctx:true env sigma body)]) [] body) in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  `Assoc [
    "id", `Int id;
    "hypotheses", `List (List.rev hyps);
    "goal", `String (Pp.string_of_ppcmds ccl)
  ]


let mk_proofview Proof.{ goals; sigma } =
  let goals = List.map (mk_goal sigma) goals in
  let shelved = List.map (mk_goal sigma) (Evd.shelf sigma) in
  let given_up = List.map (mk_goal sigma) (Evar.Set.elements @@ Evd.given_up sigma) in
  `Assoc [
    "type", `String "proof-view";
    "goals", `List goals;
    "shelvedGoals", `List shelved;
    "abandonedGoals", `List given_up
  ]

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
    Dm.Types.Range.{ start; stop }, text
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

let inject_dm_events (uri,l) =
  List.map (inject_dm_event uri) l

let coqtopUpdateProofView ~id params = 
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let loc = params |> member "location" |> parse_loc in
  let st = Hashtbl.find states uri in
  match Dm.DocumentManager.get_proof st loc with
  | None -> ()
  | Some proofview ->
    let result = mk_proofview proofview in
    output_json @@ mk_response ~id ~result 


let dispatch_method ~id method_name params : events =
  match method_name with
  | "initialize" -> do_initialize ~id; []
  | "initialized" -> []
  | "textDocument/didOpen" -> textDocumentDidOpen params |> inject_dm_events
  | "textDocument/didChange" -> textDocumentDidChange params |> inject_dm_events
  | "textDocument/didSave" -> textDocumentDidSave params; []
  | "vscoq/interpretToPoint" -> coqtopInterpretToPoint ~id params |> inject_dm_events
  | "vscoq/stepBackward" -> coqtopStepBackward ~id params |> inject_dm_events
  | "vscoq/stepForward" -> coqtopStepForward ~id params |> inject_dm_events
  | "vscoq/resetCoq" -> coqtopResetCoq ~id params; []
  | "vscoq/interpretToEnd" -> coqtopInterpretToEnd ~id params |> inject_dm_events
  | "vscoq/updateProofView" -> coqtopUpdateProofView ~id params; []
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
      more_events @ [lsp]

let pr_lsp_event = function
  | Request req ->
    Pp.str "Request"

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

let pr_event = function
  | LspManagerEvent e -> pr_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    Dm.DocumentManager.pr_event e

let init injections =
  init_state := Some (Vernacstate.freeze_interp_state ~marshallable:false, injections)


