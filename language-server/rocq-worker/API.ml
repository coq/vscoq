module Pure = struct

  let string_of_ppcmds = Pp.string_of_ppcmds
  let fold_left_map = CList.fold_left_map
    
  let severity_of_feedback_level = let open Protocol.LspWrapper.DiagnosticSeverity in function
    | Feedback.Error -> Error
    | Feedback.Warning -> Warning
    | Feedback.(Info | Debug | Notice) -> Information
  
  let channel_of_feedback_level = let open Protocol.LspWrapper.FeedbackChannel in function
    | Feedback.Debug -> Some Debug
    | Feedback.Info -> Some Info 
    | Feedback.Notice -> Some Notice 
    | Feedback.(Error | Warning) -> None
  
  let is_section_begin ast =
    let open Vernacexpr in
    let open Synterp in
    match ast.CAst.v.expr with
    | VernacSynterp (EVernacBeginSection _) -> true
    | _ -> false
  let is_section_end ast =
    let open Vernacexpr in
    let open Synterp in
    match ast.CAst.v.expr with
    | VernacSynterp (EVernacEndSegment _) -> true
    | _ -> false

  let pp_of_coq_pp = Printing.pp_of_coqpp

end

module DelegationManager = DelegationManager

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
  
let get_hover_contents = Hover.get_hover_contents

let get_proof = ProofState.get_proof

let find_proof_using (ast : Synterp.vernac_control_entry) =
  match ast.CAst.v.expr with
  | VernacSynPure(VernacProof(_,Some e)) -> Some e
  | _ -> Proof_using.get_default_proof_using ()

(* TODO: There is also a #[using] annotation on the proof opener we should
   take into account (but it is not on a proof sentence, but rather
   on the proof opener). Ask maxime if the attribute is processed during
   synterp, and if so where its value is stored. *)
let find_proof_using_annotation proof_sentences =
  match List.rev proof_sentences with
  | (_,ast) :: _ -> find_proof_using ast
  | _ -> None

let is_opaque_flat_proof terminator ~section_depth proof_sentences =
  let open Vernacextend in
  let has_side_effect (classif,_) = match classif with
    | VtStartProof _ | VtSideff _ | VtQed _ | VtProofMode _ | VtMeta -> true
    | VtProofStep _ | VtQuery -> false
  in
  if List.exists has_side_effect proof_sentences then None
  else match terminator with
  | VtDrop -> Some Vernacexpr.SsEmpty
  | VtKeep VtKeepDefined -> None
  | VtKeep (VtKeepAxiom | VtKeepOpaque) ->
      if section_depth = 0 then Some Vernacexpr.SsEmpty
      else find_proof_using_annotation proof_sentences
    

open Gramlib

[%%if coq = "8.18" || coq = "8.19"]
let parse_one_sentence ?loc stream =
  Vernacstate.Synterp. st;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Pcoq.Parsable.make ?loc stream in
  let sentence = Pcoq.Entry.parse entry pa in
  (sentence, [])
[%%elif coq = "8.20"]
let parse_one_sentence ?loc stream =
  Flags.record_comments := true;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Pcoq.Parsable.make ?loc stream in
  let sentence = Pcoq.Entry.parse entry pa in
  let comments = Pcoq.Parsable.comments pa in
  (sentence, comments)
[%%else]
let parse_one_sentence ?loc stream =
  Flags.record_comments := true;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Procq.Parsable.make ?loc stream in
  let sentence = Procq.Entry.parse entry pa in
  let comments = Procq.Parsable.comments pa in
  (sentence, comments)
[%%endif]

[%%if coq = "8.18" || coq = "8.19"]
let get_loc_from_info_or_exn e info =
  match e with
  | Synterp.UnmappedLibrary (_, qid) -> qid.loc
  | Synterp.NotFoundLibrary (_, qid) -> qid.loc
  | _ -> Loc.get_loc @@ info
[%%else]
let get_loc_from_info_or_exn _ info =
  Loc.get_loc info

(* let get_qf_from_info info = Quickfix.get_qf info *)
[%%endif]

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let get_keyword_state = Pcoq.get_keyword_state
[%%else]
  let get_keyword_state = Procq.get_keyword_state
[%%endif]
    
    

let rec stream_tok n_tok acc str begin_line begin_char =
  let e = LStream.next (get_keyword_state ()) str in
  match e with
  | Tok.EOI ->
    List.rev acc
  | _ ->
    stream_tok (n_tok+1) (e::acc) str begin_line begin_char
    (*
let parse_one_sentence stream ~st =
  let pa = Pcoq.Parsable.make stream in
  Vernacstate.Parser.parse st (Pvernac.main_entry (Some (Vernacinterp.get_default_proof_mode ()))) pa
  (* FIXME: handle proof mode correctly *)
  *)
type parser_result = {
  ast : Vernacexpr.vernac_control;
  loc : Loc.t;
  stop : int;
  begin_char : int;
  tokens : Tok.t list;
  comments : ((int * int) * string) list;
}
type synterp_result = {
  parsed : parser_result;
  ast : Synterp.vernac_control_entry;
  classification : Vernacextend.vernac_classification;
  synterp_state : Vernacstate.Synterp.t;
}

exception Error of Loc.t option * Pp.t * Types.Quickfix.t list option

let with_err f x =
  try f x with e ->
    let e, i = Exninfo.capture e in
    let loc = get_loc_from_info_or_exn e i in
    let qf = Result.value ~default:[] @@ Types.Quickfix.from_exception e in
    Exninfo.iraise (Error (loc,CErrors.iprint_no_report (e, i),Some qf),i)

exception ParseError of Loc.t option * Pp.t * Types.Quickfix.t list option
exception SynterpError of parser_result * Loc.t option * Pp.t * Types.Quickfix.t list option

[%%if coq = "8.18" || coq = "8.19"]
let synterp_ast ast = Synterp.synterp_control ast
[%%else]
let synterp_ast ast =
  let intern = Vernacinterp.fs_intern in
  Synterp.synterp_control ~intern ast
[%%endif]

let parse_one_sentence ?loc txt stream ~st =
  Vernacstate.Synterp.unfreeze st;
  let p, comments = parse_one_sentence ?loc stream in
  match p with
  | None -> None
  | Some ast ->
      let stop = Stream.count stream in
      let loc = match ast.loc with None -> assert false | Some x -> x in
      let begin_line, begin_char, end_char = loc.line_nb, loc.bp, loc.ep in
      let str = String.sub txt begin_char (end_char - begin_char) in
      let sstr = Stream.of_string str in
      let lex = CLexer.Lexer.tok_func sstr in
      let tokens = stream_tok 0 [] lex begin_line begin_char in
      Some { ast; loc; stop; begin_char; tokens; comments }

let synterp_one_sentence ({ ast } as parsed : parser_result) =
  let classification = Vernac_classifier.classify_vernac ast in
  let ast = synterp_ast ast in
  let synterp_state = Vernacstate.Synterp.freeze () in
  { parsed; ast; classification; synterp_state; }

let with_parse_err f x =
  try f x with e ->
    let e, i = Exninfo.capture e in
    let loc = get_loc_from_info_or_exn e i in
    let qf = Result.value ~default:[] @@ Types.Quickfix.from_exception e in
    Exninfo.iraise (ParseError (loc,CErrors.iprint_no_report (e, i),Some qf),i)
  
let with_synterp_err f p =
  try f p with e ->
    let e, i = Exninfo.capture e in
    let loc = get_loc_from_info_or_exn e i in
    let qf = Result.value ~default:[] @@ Types.Quickfix.from_exception e in
    Exninfo.iraise (SynterpError (p,loc,CErrors.iprint_no_report (e, i),Some qf),i)

let parse_and_synterp_one_sentence_err ?loc t stream ~st =
  with_parse_err (parse_one_sentence ?loc t ~st) stream |>
  Option.map @@ with_synterp_err synterp_one_sentence

let rec junk_sentence_end stream =
  match Stream.npeek () 2 stream with
  | ['.'; (' ' | '\t' | '\n' |'\r')] -> Stream.junk () stream
  | [] -> ()
  | _ ->  Stream.junk () stream; junk_sentence_end stream

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
let init ~usage opts =
  Coqinit.init_ocaml ();
  let _injections = Coqinit.init_runtime opts in
  Safe_typing.allow_delayed_constants := true; (* Needed to delegate or skip proofs *)
  Flags.load_vos_libraries := true;
  Sys.(set_signal sigint Signal_ignore);
[%%else]
let init ~usage opts =
  Coqinit.init_ocaml ();
  let () = Coqinit.init_runtime ~usage opts in
  Safe_typing.allow_delayed_constants := true; (* Needed to delegate or skip proofs *)
  Flags.load_vos_libraries := true;
  Sys.(set_signal sigint Signal_ignore);
[%%endif]


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
let parse_entry st entry pattern =
  let pa = Pcoq.Parsable.make (Gramlib.Stream.of_string pattern) in
  let st = st.Vernacstate.Synterp.parsing in
  with_parse_err (Vernacstate.Parser.parse st entry) pa
[%%else]
let parse_entry st entry pattern =
  let pa = parsable_make (Gramlib.Stream.of_string pattern) in
  Vernacstate.Synterp.unfreeze st;
  with_parse_err (entry_parse entry) pa
[%%endif]

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let smart_global = Pcoq.Prim.smart_global
[%%else]
  let smart_global = Procq.Prim.smart_global
[%%endif]
[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  let lconstr = Pcoq.Constr.lconstr
[%%else]
  let lconstr = Procq.Constr.lconstr
[%%endif]

  

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
let jump_to_definition _ _ _ = None
[%%else]
let jump_to_definition pst vst pattern =
    try
    let qid = parse_entry pst (Procq.Prim.qualid) pattern in
      let ref = Nametab.locate_extended qid in
      (* TODO vst <> None *)
        match Nametab.cci_src_loc ref with
          | None -> None
          | Some loc ->
            begin match loc.Loc.fname with
              | Loc.ToplevelInput | InFile  { dirpath = None } -> None
              | InFile { dirpath = Some dp } ->
                  let f = Loadpath.locate_absolute_library @@ Libnames.dirpath_of_string dp in
                  begin match f with
                    | Ok f ->
                      let f =  Filename.remove_extension f ^ ".v" in
                      (if Sys.file_exists f then
                        Some (loc, f)
                      else
                        None
                      )
                    | Error _ -> None
                  end
            end
        with e ->
          let e, info = Exninfo.capture e in
          log (fun () -> Pp.string_of_ppcmds @@ CErrors.iprint (e, info)); None

[%%endif]
  
let print_about = Prettyp.print_about
let check_may_eval = Vernacentries.check_may_eval
[%%if coq = "8.18" || coq = "8.19"]
let print_located_qualid _ qid = Prettyp.print_located_qualid qid
[%%else]
let print_located_qualid = Prettyp.print_located_qualid
[%%endif]
let print_located_qualid env sigma q =
  let open Constrexpr in
  match q with
  | { CAst.v = AN qid } ->  (print_located_qualid env qid)
  | { v = ByNotation (ntn, sc)} ->
    ( Notation.locate_notation
      (Constrextern.without_symbols (Printer.pr_glob_constr_env env sigma)) ntn sc)
let search_queries = G_vernac.search_queries
[%%if coq = "8.18" || coq = "8.19"]
let print_name env sigma n = Prettyp.print_name env sigma n
[%%else]
let print_name env sigma n =
  let access = Library.indirect_accessor[@@warning "-3"] in
  Prettyp.print_name access env sigma n None
[%%endif]
      
      
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

let start_library ~init_vs ~path opts =
  Vernacstate.unfreeze_full_state init_vs;
  let top = dirpath_of_top (TopPhysical path) in
  start_library top opts;
  Vernacstate.freeze_full_state ()
