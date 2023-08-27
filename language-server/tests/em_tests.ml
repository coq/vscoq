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
open Common

[@@@warning "-27"]

let set_delegation_mode mode =
  ExecutionManager.(set_options { delegation_mode = mode; completion_options = { enable = false; unificationLimit = 100; algorithm = StructuredSplitUnification; atomicFactor = 5.; sizeFactor = 5. }; enableDiagnostics = true })

let%test_unit "exec: finished proof" =
  let st, init_events = init_test_doc ~text:"Lemma x : True. trivial. Qed. Check x." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(P(P O)))) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s4.id,Information,".*True.*")
  ]

let%test_unit "exec: finished proof skip" =
  let st, init_events = init_test_doc ~text:"Lemma x : True. trivial. Qed. Check x." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(P(P O)))) in
  set_delegation_mode SkipProofs;
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s4.id,Information,".*True.*")
  ];
  ExecutionManager.set_default_options ()

let%test_unit "exec: unfinished proof" =
  let st, init_events = init_test_doc ~text:"Lemma x : True. Qed. Check x." in
  let st, (s1, (s2, (s3, ()))) = dm_parse st (P(P(P O))) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  let errors = ExecutionManager.all_errors (DocumentManager.Internal.execution_state st) in
  [%test_eq: bool] true (1 = List.length errors);
  check_diag st [
    D (s2.id,Error,".*incomplete proof.*");
  ];
  check_diag st [
    D (s3.id,Information,".*True.*")
  ]

let%test_unit "exec: unfinished proof skip" =
  let st, init_events = init_test_doc ~text:"Lemma x : True. Qed. Check x." in
  let st, (s1, (s2, (s3, ()))) = dm_parse st (P(P(P O))) in
  set_delegation_mode SkipProofs;
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s2.id,Error,".*incomplete proof.*")
  ];
  check_diag st [
    D (s3.id,Information,".*True.*")
  ];
  ExecutionManager.set_default_options ()

let%test_unit "exec: unfinished proof delegate" =
  let st, init_events = init_test_doc ~text:"Lemma x : True. Qed. Check x." in
  let st, (s1, (s2, (s3, ()))) = dm_parse st (P(P(P O))) in
  set_delegation_mode (DelegateProofsToWorkers { number_of_workers = 1 });
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s2.id,Error,".*incomplete proof.*")
  ];
  check_diag st [
    D (s3.id,Information,".*True.*")
  ];
  ExecutionManager.set_default_options ()


let%test_unit "exec: unstarted proof" =
  let st, init_events = init_test_doc ~text:"Qed. Check nat." in
  let st, (s1, (s2, ())) = dm_parse st (P(P O)) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  check_diag st [
    D (s1.id,Error,".*No proof-editing in progress.*");
  ];
  check_diag st [
    D (s2.id,Information,".*Set.*")
  ]
