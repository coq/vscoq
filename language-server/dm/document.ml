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
open Gramlib
open Types
open Lsp.Types
open Scheduler

let Log log = Log.mk_log "document"

module LM = Map.Make (Int)

module SM = Map.Make (Stateid)

type proof_block_type =
  | TheoremKind of Decls.theorem_kind
  | DefinitionType of Decls.definition_object_kind
  | InductiveType of Vernacexpr.inductive_kind
  | Other

type proof_step = {
  id: sentence_id;
  tactic: string;
  range: Range.t;
}

type outline_element = {
  id: sentence_id;
  name: string;
  type_: proof_block_type;
  statement: string;
  proof: proof_step list;
  range: Range.t
}

type outline = outline_element list

type parsed_ast = {
  ast: Synterp.vernac_control_entry;
  classification: Vernacextend.vernac_classification;
  tokens: Tok.t list
}

type comment = {
  start: int;
  stop: int;
  content: string;
}

type parsing_error = {
  start: int;
  stop: int;
  msg: Pp.t Loc.located;
  qf: Quickfix.t list option;
}

type sentence_state =
  | Error of parsing_error
  | Parsed of parsed_ast

type pre_sentence = {
  parsing_start : int;
  start : int;
  stop : int;
  synterp_state : Vernacstate.Synterp.t; (* synterp state after this sentence's synterp phase *)
  ast : sentence_state;
}

(* Example:                        *)
(* "  Check 3. "                   *)
(* ^  ^       ^---- end            *)
(* |  |------------ start          *)
(* |---------------- parsing_start *)
type sentence = {
  parsing_start : int;
  start : int;
  stop : int;
  synterp_state : Vernacstate.Synterp.t; (* synterp state after this sentence's synterp phase *)
  scheduler_state_before : Scheduler.state;
  scheduler_state_after : Scheduler.state;
  ast : sentence_state;
  id : sentence_id;
}

type document = {
  sentences_by_id : sentence SM.t;
  sentences_by_end : sentence LM.t;
  parsing_errors_by_end : parsing_error LM.t;
  comments_by_end : comment LM.t;
  schedule : Scheduler.schedule;
  outline : outline;
  parsed_loc : int;
  raw_doc : RawDocument.t;
  init_synterp_state : Vernacstate.Synterp.t;
  cancel_handle: Sel.Event.cancellation_handle option;
}

type parse_state = {
  started: float;
  stop: int;
  top_id: sentence_id option;
  loc: Loc.t option;
  synterp_state : Vernacstate.Synterp.t;
  stream: (unit, char) Gramlib.Stream.t;
  raw: RawDocument.t;
  parsed: pre_sentence list;
  errors: parsing_error list;
  parsed_comments: comment list;
  previous_document: document;
}

type parsing_end_info = {
    unchanged_id: sentence_id option;
    invalid_ids: sentence_id_set;
    previous_document: document;
    parsed_document: document;
}

type event = 
| ParseEvent of parse_state
| Invalidate of parse_state
let pp_event fmt = function
 | ParseEvent _ -> Format.fprintf fmt "ParseEvent _"
 | Invalidate _ -> Format.fprintf fmt "Invalidate _"

type events = event Sel.Event.t list

let create_parsing_event event =
  let priority = Some PriorityManager.parsing in
  Sel.now ?priority event

let range_of_sentence raw (sentence : sentence) =
  let start = RawDocument.position_of_loc raw sentence.start in
  let end_ = RawDocument.position_of_loc raw sentence.stop in
  Range.{ start; end_ }

let string_of_sentence raw (sentence: sentence) =
    let string = RawDocument.string_in_range raw sentence.start sentence.stop in
    string

let range_of_sentence_with_blank_space raw (sentence : sentence) =
  let start = RawDocument.position_of_loc raw sentence.parsing_start in
  let end_ = RawDocument.position_of_loc raw sentence.stop in
  Range.{ start; end_ }

let string_of_id document id =
  match SM.find_opt id document.sentences_by_id with
  | None -> CErrors.anomaly Pp.(str"Trying to get range of non-existing sentence " ++ Stateid.print id)
  | Some sentence -> string_of_sentence document.raw_doc sentence

let range_of_id document id =
  match SM.find_opt id document.sentences_by_id with
  | None -> CErrors.anomaly Pp.(str"Trying to get range of non-existing sentence " ++ Stateid.print id)
  | Some sentence -> range_of_sentence document.raw_doc sentence

let range_of_id_with_blank_space document id =
  match SM.find_opt id document.sentences_by_id with
  | None -> CErrors.anomaly Pp.(str"Trying to get range of non-existing sentence " ++ Stateid.print id)
  | Some sentence -> range_of_sentence_with_blank_space document.raw_doc sentence

let push_proof_step_in_outline document id (outline : outline) =
  let range = range_of_id document id in
  let tactic = string_of_id document id in
  let proof_step = {id; tactic; range} in
  match outline with
  | [] -> outline
  | e :: l -> 
    let proof = proof_step :: e.proof in
    {e with proof} :: l

let record_outline document id (ast : Synterp.vernac_control_entry) classif (outline : outline) =
  let open Vernacextend in
  match classif with
  | VtProofStep _ | VtQed _ -> push_proof_step_in_outline document id outline
  | VtStartProof (_, names) ->
    let vernac_gen_expr = ast.v.expr in
    let type_ = match vernac_gen_expr with
      | VernacSynterp _ -> None
      | VernacSynPure pure -> 
        match pure with
        | Vernacexpr.VernacStartTheoremProof (kind, _) -> Some (TheoremKind kind)
        | Vernacexpr.VernacDefinition ((_, def), _, _) -> Some (DefinitionType def)
        | Vernacexpr.VernacFixpoint (_, _) -> Some (DefinitionType Decls.Fixpoint)
        | Vernacexpr.VernacCoFixpoint (_, _) -> Some (DefinitionType Decls.CoFixpoint)
        | _ -> None
    in
    let name = match names with
    |[] -> "default"
    | n :: _ -> Names.Id.to_string n 
    in
    begin match type_ with
    | None -> outline
    | Some type_ ->
      let range = range_of_id document id in
      let statement = string_of_id document id in
      let element = {id; type_; name; statement; range; proof=[]} in
      element :: outline
    end
  | VtSideff (names, _) ->
    let vernac_gen_expr = ast.v.expr in
    let type_, statement = match vernac_gen_expr with
      | VernacSynterp (Synterp.EVernacExtend _) when names <> [] -> Some Other, "external"
      | VernacSynterp _ -> None, ""
      | VernacSynPure pure -> 
        match pure with
        | Vernacexpr.VernacStartTheoremProof (kind, _) -> Some (TheoremKind kind), string_of_id document id
        | Vernacexpr.VernacDefinition ((_, def), _, _) -> Some (DefinitionType def), string_of_id document id
        | Vernacexpr.VernacInductive (kind, _) -> Some (InductiveType kind), string_of_id document id
        | Vernacexpr.VernacFixpoint (_, _) -> Some (DefinitionType Decls.Fixpoint), string_of_id document id
        | Vernacexpr.VernacCoFixpoint (_, _) -> Some (DefinitionType Decls.CoFixpoint), string_of_id document id
        | _ -> None, ""
    in
    let name = match names with
    |[] -> "default"
    | n :: _ -> Names.Id.to_string n 
    in
    begin match type_ with
    | None -> outline
    | Some type_ ->
      let range = range_of_id document id in
      let element = {id; type_; name; statement; range; proof=[]} in
      element :: outline
    end
  | _ -> outline

let record_outline document {id; ast} outline =
  match ast with
  | Error _ -> outline
  | Parsed ast -> record_outline document id ast.ast ast.classification outline

let compute_outline ({ sentences_by_end } as document) =
    LM.fold (fun _ s -> record_outline document s) sentences_by_end []


let schedule doc = doc.schedule

let raw_document doc = doc.raw_doc

let outline doc = doc.outline
let parse_errors parsed =
  List.map snd (LM.bindings parsed.parsing_errors_by_end)

let add_sentence parsed parsing_start start stop (ast: sentence_state) synterp_state scheduler_state_before =
  let id = Stateid.fresh () in
  let scheduler_state_after, schedule = 
    match ast with
    | Error {msg} ->
      scheduler_state_before, Scheduler.schedule_errored_sentence id msg parsed.schedule
    | Parsed ast ->
      let ast' = (ast.ast, ast.classification, synterp_state) in
      Scheduler.schedule_sentence (id, ast') scheduler_state_before parsed.schedule
  in
  (* FIXME may invalidate scheduler_state_XXX for following sentences -> propagate? *)
  let sentence = { parsing_start; start; stop; ast; id; synterp_state; scheduler_state_before; scheduler_state_after } in
  let document = { 
    parsed with sentences_by_end = LM.add stop sentence parsed.sentences_by_end;
    sentences_by_id = SM.add id sentence parsed.sentences_by_id;
    schedule;
  } in
  document, scheduler_state_after

let pre_sentence_to_sentence parsing_start start stop (ast: parsed_ast) synterp_state scheduler_state_before schedule =
  let id = Stateid.fresh () in
  let ast' = (ast.ast, ast.classification, synterp_state) in
  let scheduler_state_after, schedule =
    Scheduler.schedule_sentence (id, ast') scheduler_state_before schedule
  in
  (* FIXME may invalidate scheduler_state_XXX for following sentences -> propagate? *)
  let sentence = { parsing_start; start; stop; ast; id; synterp_state; scheduler_state_before; scheduler_state_after } in
  sentence, schedule, scheduler_state_after
  
let remove_sentence parsed id =
  match SM.find_opt id parsed.sentences_by_id with
  | None -> parsed
  | Some sentence ->
    let sentences_by_id = SM.remove id parsed.sentences_by_id in
    let sentences_by_end = LM.remove sentence.stop parsed.sentences_by_end in
    let outline = List.filter (fun (e : outline_element) -> e.id != id) parsed.outline in
    (* TODO clean up the schedule and free cached states *)
    { parsed with sentences_by_id; sentences_by_end; outline }

let sentences parsed =
  List.map snd @@ SM.bindings parsed.sentences_by_id
  
type code_line =
  | Sentence of sentence
  | ParsingError of parsing_error
  | Comment of comment
  
let start_of_code_line = function
  | Sentence { start = x } -> x
  | ParsingError  { start = x } -> x
  | Comment { start = x } -> x

let compare_code_line x y =
  let s1 = start_of_code_line x in
  let s2 = start_of_code_line y in
  s1 - s2

let code_lines_sorted_by_loc parsed =
  List.sort compare_code_line @@ List.concat [
    (List.map (fun (_,x) -> Sentence x) @@ SM.bindings parsed.sentences_by_id) ;
    (List.map (fun (_,x) -> ParsingError x) @@ LM.bindings parsed.parsing_errors_by_end) ;
    []  (* todo comments *)
   ]

let code_lines_by_end_sorted_by_loc parsed =
  List.sort compare_code_line @@ List.concat [
    (List.map (fun (_,x) -> Sentence x) @@ LM.bindings parsed.sentences_by_end) ;
    (List.map (fun (_,x) -> ParsingError x) @@ LM.bindings parsed.parsing_errors_by_end) ;
    []  (* todo comments *)
   ]

let sentences_sorted_by_loc parsed =
  List.sort (fun ({start = s1} : sentence) {start = s2} -> s1 - s2) @@ List.map snd @@ SM.bindings parsed.sentences_by_id

let sentences_before parsed loc =
  let (before,ov,_after) = LM.split loc parsed.sentences_by_end in
  let before = Option.cata (fun v -> LM.add loc v before) before ov in
  List.map (fun (_id,s) -> s) @@ LM.bindings before

let sentences_after parsed loc =
  let (_before,ov,after) = LM.split loc parsed.sentences_by_end in
  let after = Option.cata (fun v -> LM.add loc v after) after ov in
  List.map (fun (_id,s) -> s) @@ LM.bindings after

let parsing_errors_before parsed loc =
  LM.filter (fun stop _v -> stop <= loc) parsed.parsing_errors_by_end

let comments_before parsed loc =
  LM.filter (fun stop _v -> stop <= loc) parsed.comments_by_end
let get_sentence parsed id =
  SM.find_opt id parsed.sentences_by_id

let find_sentence parsed loc =
  match LM.find_first_opt (fun k -> loc <= k) parsed.sentences_by_end with
  | Some (_, sentence) when sentence.start <= loc -> Some sentence
  | _ -> None

let find_sentence_before parsed loc =
  match LM.find_last_opt (fun k -> k <= loc) parsed.sentences_by_end with
  | Some (_, sentence) -> Some sentence
  | _ -> None

let find_sentence_strictly_before parsed loc =
  match LM.find_last_opt (fun k -> k < loc) parsed.sentences_by_end with
  | Some (_, sentence) -> Some sentence
  | _ -> None

let find_sentence_after parsed loc = 
  match LM.find_first_opt (fun k -> loc <= k) parsed.sentences_by_end with
  | Some (_, sentence) -> Some sentence
  | _ -> None

let find_next_qed parsed loc =
  let exception Found of sentence in
  let f k sentence =
    if loc <= k then
    match sentence.ast with
    | Error _ -> ()
    | Parsed ast ->
    match ast.classification with
      | VtQed _ -> raise (Found sentence)
      | _ -> () in
  (* We can't use find_first since f isn't monotone *)
  match LM.iter f parsed.sentences_by_end with
  | () -> None
  | exception (Found n) -> Some n

let get_first_sentence parsed = 
  Option.map snd @@ LM.find_first_opt (fun _ -> true) parsed.sentences_by_end

let get_last_sentence parsed = 
  Option.map snd @@ LM.find_last_opt (fun _ -> true) parsed.sentences_by_end

let state_after_sentence parsed = function
  | Some (stop, { synterp_state; scheduler_state_after }) ->
    (stop, synterp_state, scheduler_state_after)
  | None -> (-1, parsed.init_synterp_state, Scheduler.initial_state)

let state_at_pos parsed pos =
  state_after_sentence parsed @@
    LM.find_last_opt (fun stop -> stop <= pos) parsed.sentences_by_end

let state_strictly_before parsed pos =
  state_after_sentence parsed @@
    LM.find_last_opt (fun stop -> stop < pos) parsed.sentences_by_end

let pos_at_end parsed =
  match LM.max_binding_opt parsed.sentences_by_end with
  | Some (stop, _) -> stop
  | None -> -1

let string_of_parsed_ast { tokens } = 
  (* TODO implement printer for vernac_entry *)
  "[" ^ String.concat "--" (List.map (Tok.extract_string false) tokens) ^ "]"

let string_of_parsed_ast = function
| Error _ -> "errored sentence"
| Parsed ast -> string_of_parsed_ast ast

let patch_sentence parsed scheduler_state_before id ({ parsing_start; ast; start; stop; synterp_state } : pre_sentence) =
  let old_sentence = SM.find id parsed.sentences_by_id in
  log (fun () -> Format.sprintf "Patching sentence %s , %s" (Stateid.to_string id) (string_of_parsed_ast old_sentence.ast));
  let scheduler_state_after, schedule =
    match ast with
    | Error {msg} ->
      scheduler_state_before, Scheduler.schedule_errored_sentence id msg parsed.schedule
    | Parsed ast ->
      let ast = (ast.ast, ast.classification, synterp_state) in
      Scheduler.schedule_sentence (id,ast) scheduler_state_before parsed.schedule
  in
  let new_sentence = { old_sentence with ast; parsing_start; start; stop; scheduler_state_before; scheduler_state_after } in
  let sentences_by_id = SM.add id new_sentence parsed.sentences_by_id in
  let sentences_by_end = match LM.find_opt old_sentence.stop parsed.sentences_by_end with
  | Some { id } when Stateid.equal id new_sentence.id ->
    LM.remove old_sentence.stop parsed.sentences_by_end 
  | _ -> parsed.sentences_by_end
  in
  let sentences_by_end = LM.add new_sentence.stop new_sentence sentences_by_end in
  { parsed with sentences_by_end; sentences_by_id; schedule }, scheduler_state_after

type diff =
  | Deleted of sentence_id list
  | Added of pre_sentence list
  | Equal of (sentence_id * pre_sentence) list

let tok_equal t1 t2 =
  let open Tok in
  match t1, t2 with
  | KEYWORD s1, KEYWORD s2 -> CString.equal s1 s2
  | IDENT s1, IDENT s2 -> CString.equal s1 s2
  | FIELD s1, FIELD s2 -> CString.equal s1 s2
  | NUMBER n1, NUMBER n2 -> NumTok.Unsigned.equal n1 n2
  | STRING s1, STRING s2 -> CString.equal s1 s2
  | LEFTQMARK, LEFTQMARK -> true
  | BULLET s1, BULLET s2 -> CString.equal s1 s2
  | EOI, EOI -> true
  | QUOTATION(s1,t1), QUOTATION(s2,t2) -> CString.equal s1 s2 && CString.equal t1 t2
  | _ -> false

let same_tokens (s1 : sentence) (s2 : pre_sentence) =
  match s1.ast, s2.ast with
  | Error _, Error _ -> false
  | Parsed ast1, Parsed ast2 ->
    CList.equal tok_equal ast1.tokens ast2.tokens
  | _, _ -> false
  
(* TODO improve diff strategy (insertions,etc) *)
let rec diff old_sentences new_sentences =
  match old_sentences, new_sentences with
  | [], [] -> []
  | [], new_sentences -> [Added new_sentences]
  | old_sentences, [] -> [Deleted (List.map (fun s -> s.id) old_sentences)]
    (* FIXME something special should be done when `Deleted` is applied to a parsing effect *)
  | old_sentence::old_sentences, new_sentence::new_sentences ->
    if same_tokens old_sentence new_sentence then 
      Equal [(old_sentence.id,new_sentence)] :: diff old_sentences new_sentences
    else 
      Deleted [old_sentence.id] :: Added [new_sentence] :: diff old_sentences new_sentences

let string_of_diff_item doc = function
  | Deleted ids ->
       ids |> List.map (fun id -> Printf.sprintf "- (id: %d) %s" (Stateid.to_int id) (string_of_parsed_ast (Option.get (get_sentence doc id)).ast))
  | Added sentences ->
       sentences |> List.map (fun (s : pre_sentence) -> Printf.sprintf "+ %s" (string_of_parsed_ast s.ast))
  | Equal l ->
       l |> List.map (fun (id, (s : pre_sentence)) -> Printf.sprintf "= (id: %d) %s" (Stateid.to_int id) (string_of_parsed_ast s.ast))

let string_of_diff doc l =
  String.concat "\n" (List.flatten (List.map (string_of_diff_item doc) l))

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


[%%if coq = "8.18" || coq = "8.19"]
let parse_one_sentence ?loc stream ~st =
  Vernacstate.Synterp.unfreeze st;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Pcoq.Parsable.make ?loc stream in
  let sentence = Pcoq.Entry.parse entry pa in
  (sentence, [])
[%%elif coq = "8.20"]
let parse_one_sentence ?loc stream ~st =
  Vernacstate.Synterp.unfreeze st;
  Flags.record_comments := true;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Pcoq.Parsable.make ?loc stream in
  let sentence = Pcoq.Entry.parse entry pa in
  let comments = Pcoq.Parsable.comments pa in
  (sentence, comments)
[%%else]
let parse_one_sentence ?loc stream ~st =
  Vernacstate.Synterp.unfreeze st;
  Flags.record_comments := true;
  let entry = Pvernac.main_entry (Some (Synterp.get_default_proof_mode ())) in
  let pa = Procq.Parsable.make ?loc stream in
  let sentence = Procq.Entry.parse entry pa in
  let comments = Procq.Parsable.comments pa in
  (sentence, comments)
[%%endif]

let rec junk_sentence_end stream =
  match Stream.npeek () 2 stream with
  | ['.'; (' ' | '\t' | '\n' |'\r')] -> Stream.junk () stream
  | [] -> ()
  | _ ->  Stream.junk () stream; junk_sentence_end stream

[%%if coq = "8.18"]
exception E = Stream.Error
[%%else]
exception E = Grammar.Error
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

[%%if coq = "8.18" || coq = "8.19"]
let get_entry ast = Synterp.synterp_control ast
[%%else]
let get_entry ast =
  let intern = Vernacinterp.fs_intern in
  Synterp.synterp_control ~intern ast
[%%endif]


let handle_parse_error start parsing_start msg qf ({stream; errors; parsed;} as parse_state) synterp_state =
  log (fun () -> "handling parse error at " ^ string_of_int start);
  let stop = Stream.count stream in
  let parsing_error = { msg; start; stop; qf} in
  let sentence = { parsing_start; ast = Error parsing_error; start; stop; synterp_state } in
  let parsed = sentence :: parsed in
  let errors = parsing_error :: errors in
  let parse_state = {parse_state with errors; parsed} in
  (* TODO: we could count the \n between start and stop and increase Loc.line_nb *)
  create_parsing_event (ParseEvent parse_state)

let handle_parse_more ({loc; synterp_state; stream; raw; parsed; parsed_comments} as parse_state) =
  let start = Stream.count stream in
  log (fun () -> "Start of parse is: " ^ (string_of_int start));
  begin
    (* FIXME should we save lexer state? *)
    match parse_one_sentence ?loc stream ~st:synterp_state with
    | None, _ (* EOI *) -> create_parsing_event (Invalidate parse_state)
    | Some ast, comments ->
      let stop = Stream.count stream in
      let begin_line, begin_char, end_char =
              match ast.loc with
              | Some lc -> lc.line_nb, lc.bp, lc.ep
              | None -> assert false
      in
      let tokens = match raw with
      | None -> []
      | Some raw ->
        let str = String.sub (RawDocument.text raw) begin_char (end_char - begin_char) in
        let sstr = Stream.of_string str in
        let lex = CLexer.Lexer.tok_func sstr in
        stream_tok 0 [] lex begin_line begin_char in
      begin
        try
          log (fun () -> "Parsed: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast));
          let entry = get_entry ast in
          let classification = Vernac_classifier.classify_vernac ast in
          let synterp_state = Vernacstate.Synterp.freeze () in
          let parsed_ast = Parsed { ast = entry; classification; tokens } in
          let sentence = { parsing_start = start; ast = parsed_ast; start = begin_char; stop; synterp_state } in
          let parsed = sentence :: parsed in
          let comments = List.map (fun ((start, stop), content) -> {start; stop; content}) comments in
          let parsed_comments = List.append comments parsed_comments in
          let loc = ast.loc in
          let parse_state = {parse_state with parsed_comments; parsed; loc; synterp_state} in
          create_parsing_event (ParseEvent parse_state)
        with exn ->
          let e, info = Exninfo.capture exn in
          let loc = get_loc_from_info_or_exn e info in
          let qf = Result.value ~default:[] @@ Quickfix.from_exception e in
          handle_parse_error start begin_char (loc, CErrors.iprint_no_report (e,info)) (Some qf) parse_state synterp_state
        end
    | exception (E _ as exn) ->
      let e, info = Exninfo.capture exn in
      let loc = get_loc_from_info_or_exn e info in
      let qf = Result.value ~default:[] @@ Quickfix.from_exception e in
      junk_sentence_end stream;
      handle_parse_error start start (loc, CErrors.iprint_no_report (e, info)) (Some qf) {parse_state with stream} synterp_state
    | exception (CLexer.Error.E _ as exn) -> (* May be more problematic to handle for the diff *)
      let e, info = Exninfo.capture exn in
      let loc = get_loc_from_info_or_exn e info in
      let qf = Result.value ~default:[] @@ Quickfix.from_exception exn in
      junk_sentence_end stream;
      handle_parse_error start start (loc,CErrors.iprint_no_report (e, info)) (Some qf) {parse_state with stream} synterp_state
    | exception exn ->
      let e, info = Exninfo.capture exn in
      let loc = Loc.get_loc @@ info in
      let qf = Result.value ~default:[] @@ Quickfix.from_exception exn in
      junk_sentence_end stream;
      handle_parse_error start start (loc, CErrors.iprint_no_report (e,info)) (Some qf) {parse_state with stream} synterp_state
  end

let rec unchanged_id id = function
  | [] -> id
  | Equal s :: diffs ->
    unchanged_id (List.fold_left (fun _ (id,_) -> Some id) id s) diffs
  | (Added _ | Deleted _) :: _ -> id

let invalidate top_edit top_id parsed_doc new_sentences =
  let rec invalidate_diff parsed_doc scheduler_state invalid_ids = function
    | [] -> invalid_ids, parsed_doc
    | Equal s :: diffs ->
      let patch_sentence (parsed_doc,scheduler_state) (id,new_s) =
        patch_sentence parsed_doc scheduler_state id new_s
      in
      let parsed_doc, scheduler_state = List.fold_left patch_sentence (parsed_doc, scheduler_state) s in
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
    | Deleted ids :: diffs ->
      let invalid_ids = List.fold_left (fun ids id -> Stateid.Set.add id ids) invalid_ids ids in
      let parsed_doc = List.fold_left remove_sentence parsed_doc ids in
      (* FIXME update scheduler state, maybe invalidate after diff zone *)
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
    | Added new_sentences :: diffs ->
    (* FIXME could have side effect on the following, unchanged sentences *)
      let add_sentence (parsed_doc,scheduler_state) ({ parsing_start; start; stop; ast; synterp_state } : pre_sentence) =
        add_sentence parsed_doc parsing_start start stop ast synterp_state scheduler_state
      in
      let parsed_doc, scheduler_state = List.fold_left add_sentence (parsed_doc,scheduler_state) new_sentences in
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
  in
  let (_,_synterp_state,scheduler_state) = state_at_pos parsed_doc top_edit in
  let sentence_strings = LM.bindings @@ LM.map (fun s -> string_of_parsed_ast s.ast) parsed_doc.sentences_by_end in
  let sentence_strings = List.map (fun s -> snd s) sentence_strings in
  let sentence_string = String.concat " " sentence_strings in
  let sentence_strings_id = SM.bindings @@ SM.map (fun s -> string_of_parsed_ast s.ast) parsed_doc.sentences_by_id in
  let sentence_strings_id = List.map (fun s -> snd s) sentence_strings_id in
  let sentence_string_id = String.concat " " sentence_strings_id in
  log (fun () -> Format.sprintf "Top edit: %i, Doc: %s, Doc by id: %s" top_edit sentence_string sentence_string_id);
  let old_sentences = sentences_after parsed_doc top_edit in
  let diff = diff old_sentences new_sentences in
  let unchanged_id = unchanged_id top_id diff in
  log (fun () -> "diff:\n" ^ string_of_diff parsed_doc diff);
  let invalid_ids, doc = invalidate_diff parsed_doc scheduler_state Stateid.Set.empty diff in
  unchanged_id, invalid_ids, doc

(** Validate document when raw text has changed *)
let validate_document ({ parsed_loc; raw_doc; cancel_handle } as document) =
  (* Cancel any previous parsing event *)
  Option.iter Sel.Event.cancel cancel_handle;
  (* We take the state strictly before parsed_loc to cover the case when the
  end of the sentence is editted *)
  let (stop, synterp_state, _scheduler_state) = state_strictly_before document parsed_loc in
  (* let top_id = find_sentence_strictly_before document parsed_loc with None -> Top | Some sentence -> Id sentence.id in *)
  let top_id = Option.map (fun sentence -> sentence.id) (find_sentence_strictly_before document parsed_loc) in
  let text = RawDocument.text raw_doc in
  let stream = Stream.of_string text in
  while Stream.count stream < stop do Stream.junk () stream done;
  log (fun () -> Format.sprintf "Parsing more from pos %i" stop);
  let started = Unix.gettimeofday () in
  let parsed_state = {stop; top_id;synterp_state; stream; raw=raw_doc; parsed=[]; errors=[]; parsed_comments=[]; loc=None; started; previous_document=document} in
  let priority = Some PriorityManager.parsing in
  let event = Sel.now ?priority (ParseEvent parsed_state) in
  let cancel_handle = Some (Sel.Event.get_cancellation_handle event) in
  {document with cancel_handle}, [Sel.now ?priority (ParseEvent parsed_state)]

let handle_invalidate {parsed; errors; parsed_comments; stop; top_id; started; previous_document} document =
  let end_ = Unix.gettimeofday ()in
  let time = end_ -. started in
  (* log (fun () -> Format.sprintf "Parsing phase ended in %5.3f" time); *)
  log (fun () -> Format.sprintf "Parsing phase ended in %5.3f\n%!" time);
  let new_sentences = List.rev parsed in
  let new_comments = List.rev parsed_comments in
  let new_errors = errors in
  log (fun () -> Format.sprintf "%i new sentences" (List.length new_sentences));
  log (fun () -> Format.sprintf "%i new comments" (List.length new_comments));
  let errors = parsing_errors_before document stop in
  let comments = comments_before document stop in
  let unchanged_id, invalid_ids, document = invalidate (stop+1) top_id document new_sentences in
  let parsing_errors_by_end =
    List.fold_left (fun acc (error : parsing_error) -> LM.add error.stop error acc) errors new_errors
  in
  let comments_by_end =
    List.fold_left (fun acc (comment : comment) -> LM.add comment.stop comment acc) comments new_comments
  in
  let parsed_loc = pos_at_end document in
  let outline = compute_outline document in
  let parsed_document = {document with parsed_loc; parsing_errors_by_end; comments_by_end; outline} in
  Some {parsed_document; unchanged_id; invalid_ids; previous_document}

let handle_event document = function
| ParseEvent state -> 
  let event = handle_parse_more state in
  let cancel_handle = Some (Sel.Event.get_cancellation_handle event) in
  {document with cancel_handle}, [event], None
| Invalidate state -> {document with cancel_handle=None}, [], handle_invalidate state document

let parse_text_at_loc loc text document =
  let (_, synterp_state, scheduler_state) = state_strictly_before document loc in
  let stream = Stream.of_string text in
  let new_sentences, _ = parse_more synterp_state stream None in
  let add_sentence (sentences, schedule, scheduler_state) ({ parsing_start; start; stop; ast; synterp_state } : pre_sentence) =
    let added_sentence, schedule, schedule_state = pre_sentence_to_sentence parsing_start start stop ast synterp_state scheduler_state schedule in
    sentences @ [added_sentence], schedule, schedule_state
  in
  let sentences, schedule, _ = List.fold_left add_sentence ([],document.schedule, scheduler_state) new_sentences in
  sentences, schedule

let create_document init_synterp_state text =
  let raw_doc = RawDocument.create text in
    { 
      parsed_loc = -1;
      raw_doc;
      sentences_by_id = SM.empty;
      sentences_by_end = LM.empty;
      parsing_errors_by_end = LM.empty;
      comments_by_end = LM.empty;
      schedule = initial_schedule;
      outline = [];
      init_synterp_state;
      cancel_handle = None;
    }

let apply_text_edit document edit =
  let raw_doc, start = RawDocument.apply_text_edit document.raw_doc edit in
  let parsed_loc = min document.parsed_loc start in
  { document with raw_doc; parsed_loc }

let apply_text_edits document edits =
  let doc' = { document with raw_doc = document.raw_doc } in
  List.fold_left apply_text_edit doc' edits

module Internal = struct

  let string_of_sentence sentence =
    Format.sprintf "[%s] %s (%i -> %i)" (Stateid.to_string sentence.id)
    (string_of_parsed_ast sentence.ast)
    sentence.start
    sentence.stop

  let string_of_error error =
    let (_, pp) = error.msg in
    Format.sprintf "[parsing error] [%s] (%i -> %i)"
    (Pp.string_of_ppcmds pp)
    error.start
    error.stop

  let string_of_item = function
    | Sentence sentence -> string_of_sentence sentence
    | Comment _ -> "(* comment *)"
    | ParsingError error -> string_of_error error
  
end
