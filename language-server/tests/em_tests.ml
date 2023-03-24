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
open Lsp.LspData.Severity

let init text = openDoc ~uri:"doc" ~text

let%test_unit "exec: finished proof" =
  let st, init_events = init "Lemma x : True. trivial. Qed. Check x." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(P(P O)))) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.(enqueue empty init_events) in
  let todo = Sel.(enqueue todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s4.id,Notice,".*True.*")
  ]

let%test_unit "exec: unfinished proof" =
  let st, init_events = init "Lemma x : True. Qed. Check x." in
  let st, (s1, (s2, (s3, ()))) = dm_parse st (P(P(P O))) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.(enqueue empty init_events) in
  let todo = Sel.(enqueue todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s2.id,Error,".*incomplete proof.*");
    D (s3.id,Notice,".*True.*")
  ]

let%test_unit "exec: unstarted proof" =
  let st, init_events = init "Qed. Check nat." in
  let st, (s1, (s2, ())) = dm_parse st (P(P O)) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.(enqueue empty init_events) in
  let todo = Sel.(enqueue todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s1.id,Error,".*No proof-editing in progress.*");
    D (s2.id,Notice,".*Set.*")
  ]
