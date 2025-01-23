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

[%%import "vscoq_config.mlh"]

open Dm
open Base
open Types
open Protocol.LspWrapper

[%%if lsp < (1,19,0) ]
let string_of_message x = x
[%%else]
let string_of_message = function `String x -> x | _ -> assert false
[%%endif]
  
[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
let injections =
  Coqinit.init_ocaml ();
  let opts, _ = Coqargs.parse_args
    ~usage:(Boot.Usage.{executable_name = ""; extra_args = ""; extra_options = ""})
    ~init:Coqargs.default [] in
  Coqinit.init_runtime opts
[%%else]
let injections =
  Coqinit.init_ocaml ();
  let opts, _ = Coqargs.parse_args ~init:Coqargs.default [] in
  let usage = Boot.Usage.{executable_name = ""; extra_args = ""; extra_options = ""} in
  Coqinit.init_runtime ~usage opts;
  Coqinit.init_document opts;
  Coqargs.injection_commands opts
[%%endif]

let init_state = Vernacstate.freeze_full_state ()

let openDoc uri ~text =
  DocumentManager.init init_state ~opts:injections uri ~text

let run r =
  [%test_pred: (_,string) Result.t ] (function Error _ -> false | _ -> true) r;
  match r with
  | Ok x -> x
  | Error _ -> assert false
  
type simple_sentence = {
  start : int;
  stop : int;
  id : sentence_id;
}

let ss_of_s ({ start; stop; id; _ } : Document.sentence) : simple_sentence =
   { start; stop; id }

type _ parse =
  | P : 'a parse -> (simple_sentence * 'a) parse
  | E : 'a parse -> (Document.parsing_error * 'a) parse
  | O : unit parse

let rec parse : type a. int -> int -> Document.sentence list -> Document.parsing_error list -> a parse -> (a,string) Result.t =
  let open Result in
  fun m n sentences errors spec ->
    match spec, sentences, errors with
    | O, [], [] -> Ok ()
    | P spec, s :: l, errors ->
        parse (m+1) n l errors spec >>= (fun a -> Ok(ss_of_s s,a))
    | E spec, sentences, error :: l ->
        parse m (n+1) sentences l spec >>= (fun a -> Ok(error,a))
    | O, (_ :: _ as l), _ -> Error ("more sentences than expected, extra " ^ Int.to_string (List.length l))
    | O, _, (_ :: _ as l) -> Error ("more errors than expected, extra " ^ Int.to_string (List.length l))
    | P _, [], errors ->
      let errors = String.concat ~sep:"\n" @@ List.map ~f:(fun err -> Pp.string_of_ppcmds @@ snd err.Document.msg) errors in
      Error ("fewer sentences than expected, only " ^ Int.to_string m ^ "  + errors:\n" ^ errors)
    | E _, _, [] -> Error ("fewer errors than expected, only " ^ Int.to_string n)

let d_sentences doc spec =
  let sentences = Document.sentences_sorted_by_loc doc in
  let errors = Document.parse_errors doc in
  let r = run (parse 0 0 sentences errors spec) in
  r

let dm_parse st spec =
  let doc = DocumentManager.Internal.document st in
  st, d_sentences doc spec

let sentence_id_of_sexp s = Stateid.of_int (Sexplib.Std.int_of_sexp s)
let sexp_of_sentence_id i = Sexplib.Std.sexp_of_int (Stateid.to_int i)

let compare_sentence_id = Stateid.compare

type (_,'a) count =
  | O : (unit,'a) count
  | S : ('c,'a) count -> ('a * 'c, 'a) count

let rec count : type a b. int -> b list -> (a,b) count -> (a,string) Result.t =
  let open Result in
  fun n l spec ->
    match spec, l with
    | O, [] -> Ok ()
    | S spec, x :: l ->
      count (n+1) l spec >>= (fun a -> Ok(x,a))
    | O, l -> Error ("more items than expected, extra " ^ Int.to_string (List.length l))
    | S _, [] -> Error ("less items than expected, only " ^ Int.to_string n)
let count l spec = count 0 l spec

type _ task_approx =
  | Block : sentence_id task_approx
  | Exec : sentence_id task_approx
  | Skip : sentence_id task_approx
  | Query : sentence_id task_approx
  | Proof : ('a,sentence_id) count -> (sentence_id * 'a * sentence_id) task_approx

let task : type a. Scheduler.task -> a task_approx -> (a,string) Result.t =
  let open Result in
  fun t spec ->
    match spec, t with
    | Block, Block { id } -> Ok id
    | Exec, Exec { id } -> Ok id
    | Skip, Skip { id } -> Ok id
    | Query, Query { id } -> Ok id
    | Proof c, OpaqueProof { tasks; opener_id; terminator } ->
        count (List.map ~f:(fun x -> x.id) tasks) c >>= (fun l ->
        Ok (opener_id,l,terminator.id))
    | _, Skip _ -> Error "unexpected Skip"
    | _, Query _ -> Error "unexpected Query"
    | _, Exec _ -> Error "unexpected Exec"
    | _, OpaqueProof _ -> Error "unexpected OpaqueProof"
    | _, Block _ -> Error "unexpected Block"


let task st id spec =
  let sch = Document.schedule (DocumentManager.Internal.document st) in
  let init, t = Scheduler.task_for_sentence sch id in
  init, run (task t spec)


let rec handle_dm_events n (events : DocumentManager.event Sel.Todo.t) st =
  if n <= 0 then (Stdlib.Format.eprintf "handle_dm_events run out of steps:\nTodo = %a\n" (Sel.Todo.pp DocumentManager.pp_event) events; Stdlib.exit 1)
  else if Sel.Todo.is_empty events then st, events
    
  else begin
    (*Stdlib.Format.eprintf "waiting %a\n%!" Sel.(pp_todo DocumentManager.pp_event) events;*)
    Stdlib.flush_all ();
    let (ready, remaining) = Sel.pop_timeout ~stop_after_being_idle_for:0.1 events in
    match ready with
    | None -> st, events
    | Some ev ->
      (* Stdlib.Format.eprintf "handle_dm_events: handling %a\n"  DocumentManager.pp_event ev; *)
      let st, new_events =
        match DocumentManager.handle_event ev st ~block:false Protocol.Settings.Mode.Manual Protocol.Settings.Goals.Diff.Mode.Off with
        | { DocumentManager.state = None; events = events' } -> st, events'
        | { DocumentManager.state = Some st; events = events' } -> st, events'
      in
      let todo = Sel.Todo.add remaining new_events in
      handle_dm_events (n-1) todo st
  end
 

let rec handle_d_events n (events : Document.event Sel.Todo.t) (st : Document.document) : Document.parsing_end_info =
  if n <= 0 then (Stdlib.Format.eprintf "handle_d_events run out of steps:\nTodo = %a\n" (Sel.Todo.pp Document.pp_event) events; Stdlib.exit 1)
  else if Sel.Todo.is_empty events then assert false
  else begin
    (*Stdlib.Format.eprintf "waiting %a\n%!" Sel.(pp_todo DocumentManager.pp_event) events;*)
    Stdlib.flush_all ();
    let (ready, remaining) = Sel.pop_timeout ~stop_after_being_idle_for:0.1 events in
    match ready with
    | None -> assert false
    | Some ev ->
        match Document.handle_event st ev with
        | st, new_events, None ->
            let todo = Sel.Todo.add remaining new_events in
            handle_d_events (n-1) todo st
        | _, events, Some update-> assert(Sel.Todo.is_empty (Sel.Todo.add remaining events)); update
            
  end
let handle_d_events e st = handle_d_events 100 e st


type diag_spec =
  | D of sentence_id * Lsp.Types.DiagnosticSeverity.t * string

let check_no_diag st =
  let diagnostics = DocumentManager.all_diagnostics st in
  let diagnostics = List.map ~f:Lsp.Types.Diagnostic.(fun d -> d.range, string_of_message d.message, d.severity) diagnostics in
  [%test_pred: (Range.t * string * DiagnosticSeverity.t option) list] List.is_empty diagnostics

type diagnostic_summary = Range.t * string * DiagnosticSeverity.t option [@@deriving sexp]

let check_diag st specl =
  let open Result in
  let open Lsp.Types.Diagnostic in
  let diagnostic_summary { range; message; severity } =
    let message = Str.global_replace (Str.regexp_string "\n") " " (string_of_message message) in
    let message = Str.global_replace (Str.regexp " Raised at .*$") "" message in
    (range, message, severity) in
  let match_diagnostic r s rex (range, message, severity) =
    Range.included ~in_:r range &&
    Stdlib.(=) severity (Some s) &&
    Str.string_match (Str.regexp rex) message 0
  in
  let diagnostics = DocumentManager.all_diagnostics st in
  let diagnostics = List.map ~f:diagnostic_summary diagnostics in
  run @@ map_error
    ~f:(fun s -> Printf.sprintf "%s\n\nDiagnostics: %s" s (
         String.concat ~sep:"\n" (List.map ~f:(fun x -> Sexp.to_string (sexp_of_diagnostic_summary x)) diagnostics)))
    (List.fold_left ~f:(fun e c -> e >>= (fun () ->
      match c with
      | D(id,s,rex) ->
          let range = Document.range_of_id (DocumentManager.Internal.document st) id in
          match List.find ~f:(match_diagnostic range s rex) diagnostics with
          | Some _ -> Ok ()
          | None -> Error (Printf.sprintf "no %s diagnostic on %s matching %s"
                             (Sexp.to_string (DiagnosticSeverity.sexp_of_t s))
                             (Sexp.to_string (Range.sexp_of_t range))
                             rex)   
    )) ~init:(Ok ()) specl)

let test_uri = Lsp.Types.DocumentUri.of_path "foo.v"

let init_test_doc ~text = openDoc test_uri ~text
let whole_init_and_parse_test_doc ~text =
  let dm, _ = openDoc test_uri ~text in
  let doc = DocumentManager.Internal.document dm in
  let doc, events = Document.validate_document doc in
  let todo = Sel.Todo.(add empty events) in
  let update = handle_d_events todo doc in
  DocumentManager.Internal.validate_document dm update, update

let init_and_parse_test_doc ~text = snd @@ whole_init_and_parse_test_doc ~text
let dm_init_and_parse_test_doc ~text = fst @@ whole_init_and_parse_test_doc ~text


let em_init_test_doc ~text =
  let dm, init_events = openDoc test_uri ~text in
  handle_dm_events 100 Sel.Todo.(add empty init_events) dm

let handle_dm_events e st = fst @@ handle_dm_events 100 e st
  