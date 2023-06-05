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
open Base
open Dm
open Lsp
open Common

[@@@warning "-27"]

let uri = Uri.make ~scheme:"file" ~path:"foo" ()

let init text = openDoc uri ~text

let edit_text st ~start ~stop ~text =
  let doc = DocumentManager.Internal.document st in
  let doc = Document.raw_document doc in
  let start = RawDocument.position_of_loc doc start in
  let end_ = RawDocument.position_of_loc doc stop in
  let range = LspData.Range.{ start; end_ } in
  DocumentManager.apply_text_edits st [(range, text)]

  let insert_text st ~loc ~text =
    edit_text st ~start:loc ~stop:loc ~text
    
let%test_unit "parse.init" =
  let st, events = init "Definition x := true. Definition y := false." in
  let st = DocumentManager.validate_document st in
  let doc = Document.raw_document @@ DocumentManager.Internal.document st in
  [%test_eq: int] (RawDocument.end_loc doc) 44;
  let sentences = Document.sentences @@ DocumentManager.Internal.document st in
  let positions = Stdlib.List.map (fun s -> s.Document.start) sentences in
  [%test_eq: int list] positions [ 0; 22 ];
  check_no_diag st

let%test_unit "parse.insert" =
  let st, events = init "Definition x := true. Definition y := false." in
  let st = insert_text st ~loc:0 ~text:"Definition z := 0. " in
  let st = DocumentManager.validate_document st in
  let sentences = Document.sentences @@ DocumentManager.Internal.document st in
  let positions = Stdlib.List.map (fun s -> s.Document.start) sentences in
  [%test_eq: int list] positions [ 0; 19; 41 ];
  check_no_diag st

let%test_unit "parse.squash" =
  let st, events = init "Definition x := true. Definition y := false. Definition z := 0." in
  let st = edit_text st ~start:20 ~stop:21 ~text:"" in
  let st = DocumentManager.validate_document st in
  let doc = DocumentManager.Internal.document st in
  let sentences = Document.sentences doc in
  let start_positions = Stdlib.List.map (fun s -> s.Document.start) sentences in
  let stop_positions = Stdlib.List.map (fun s -> s.Document.stop) sentences in
  [%test_eq: int list] start_positions [ 44 ];
  [%test_eq: int list] stop_positions [ 62 ];
  [%test_eq: int] (List.length (Document.parse_errors doc)) 1

let%test_unit "parse.error_recovery" =
  let st, events = init "## . Definition x := true. !! . Definition y := false." in
  let st = DocumentManager.validate_document st in
  let doc = DocumentManager.Internal.document st in
  let sentences = Document.sentences doc in
  let start_positions = Stdlib.List.map (fun s -> s.Document.start) sentences in
  [%test_eq: int list] start_positions [ 5; 32 ];
  [%test_eq: int] (List.length (Document.parse_errors doc)) 2

let%test_unit "parse.extensions" =
  let st, events = init "Notation \"## x\" := x (at level 0). Definition f (x : nat) := ##xx." in
  let st = DocumentManager.validate_document st in
  let sentences = Document.sentences @@ DocumentManager.Internal.document st in
  let start_positions = Stdlib.List.map (fun s -> s.Document.start) sentences in
  [%test_eq: int list] start_positions [ 0; 35 ];
  check_no_diag st

let%test_unit "exec.init" =
  let st, init_events = init "Definition x := true. Definition y := false." in
  let st = DocumentManager.validate_document st in
  let st, events = DocumentManager.interpret_to_end st in
  let todo = Sel.(enqueue empty init_events) in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  let ranges = (DocumentManager.executed_ranges st).checked in
  let positions = Stdlib.List.map (fun s -> s.LspData.Range.start.character) ranges in
  [%test_eq: int list] positions [ 0 ];
  let positions = Stdlib.List.map (fun s -> s.LspData.Range.end_.character) ranges in
  [%test_eq: int list] positions [ 44 ];
  check_no_diag st

let%test_unit "exec.require_error" =
  let st, init_events = init "Require fuhidkgjh. Definition x := true." in
  let st, (s1, (s2, ())) = dm_parse st (E(P O)) in
  let st, events = DocumentManager.interpret_to_end st in
  let todo = Sel.(enqueue empty init_events) in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  let ranges = (DocumentManager.executed_ranges st).checked in
  let positions = Stdlib.List.map (fun s -> s.LspData.Range.start.character) ranges in
  [%test_eq: int list] positions [ 19 ]

let%test_unit "step_forward.delete_observe_id" =
  let st, init_events = init "Definition x := 3. Lemma foo : x = 3." in 
  let st, (s1, (s2, ())) = dm_parse st (P(P O)) in
  let todo = Sel.(enqueue empty init_events) in
  let st, events = DocumentManager.interpret_to_next st in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  let st, events = DocumentManager.interpret_to_next st in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  [%test_pred: sentence_id option] (Option.equal Stateid.equal (Some s2.id)) (DocumentManager.Internal.observe_id st);
  let doc = DocumentManager.Internal.document st in
  let st = DocumentManager.apply_text_edits st [Document.range_of_id doc s2.id,""] in
  [%test_pred: sentence_id option] (Option.equal Stateid.equal (Some s1.id)) (DocumentManager.Internal.observe_id st)

  let%test_unit "step_forward.proof_view" =
  let st, init_events = init "Definition x := 3. Lemma foo : x = 3." in 
  let st, (s1, (s2, ())) = dm_parse st (P(P O)) in
  let todo = Sel.(enqueue empty init_events) in
  let st, events = DocumentManager.interpret_to_next st in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  let st, events = DocumentManager.interpret_to_next st in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  let st, events = DocumentManager.interpret_to_next st in
  let todo = Sel.(enqueue todo events) in
  let st = handle_events todo st in
  [%test_pred: sentence_id option] (Option.equal Stateid.equal (Some s2.id)) (DocumentManager.Internal.observe_id st);
  let data = DocumentManager.get_proof st None in
  [%test_eq: bool] (Option.is_some data) true
  (* 
  let doc = DocumentManager.Internal.document st in
  let st = DocumentManager.apply_text_edits st [Document.range_of_id doc s2.id,""] in 
  [%test_pred: sentence_id option] (Option.equal Stateid.equal (Some s1.id)) (DocumentManager.Internal.observe_id st) *)

  let%test_unit "step_forward.document_begin" =
  let st, init_events = init "(* Some comment *)\nLemma foo : x = 3." in
  let st, (s1, ()) = dm_parse st (P O) in
  let todo = Sel.(enqueue empty init_events) in
  let st, events = DocumentManager.interpret_to_next st in
  let st = handle_events todo st in 
  [%test_pred: sentence_id option] (Option.equal Stateid.equal (Some s1.id)) (DocumentManager.Internal.observe_id st)

  let%test_unit "step_backward.document_begin" =
  let st, init_events = init "(* Some comment *)\nLemma foo : x = 3." in
  let st, (s1, ()) = dm_parse st (P O) in
  let todo = Sel.(enqueue empty init_events) in
  let st, events = DocumentManager.interpret_to_next st in
  let st = handle_events todo st in
  let todo = Sel.(enqueue empty init_events) in
  let st, events = DocumentManager.interpret_to_previous st in
  let st = handle_events todo st in
  [%test_eq: bool] (Option.is_none (DocumentManager.Internal.observe_id st)) true
  
(*
let%test_unit "exec.insert" =
  let st, events = init "Definition x := true. Definition y := false." in
  (* let st = handle_events events st in *)
  let st = DocumentManager.validate_document st in
  let st, events = DocumentManager.interpret_to_end st in
  let st = insert_text st ~loc:0 ~text:"Definition z := 0. " in
  let st = DocumentManager.validate_document st in
  let st, events = DocumentManager.interpret_to_end st in
  let ranges = (DocumentManager.executed_ranges st).checked in
  let positions = Stdlib.List.map (fun s -> s.LspData.Range.start.char) ranges in
  check_no_diag st;
  [%test_eq: int list] positions [ 0; 22 ]
  *)
