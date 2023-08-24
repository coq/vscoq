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

let%test_unit "goals: encoding after replay from top" =
  let st, init_events = init_test_doc ~text:"Lemma foo : forall x y, x + y = y + x." in
  let st, (_s1, ()) = dm_parse st (P O) in
  let st, exec_events = DocumentManager.interpret_to_next st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  let st, exec_events = DocumentManager.interpret_to_previous st in
  let todo = Sel.Todo.(add empty exec_events) in
  let st = handle_events todo st in
  let st, exec_events = DocumentManager.interpret_to_next st in
  let todo = Sel.Todo.(add empty exec_events) in
  let st = handle_events todo st in
  let proof = Stdlib.Option.get (DocumentManager.get_proof st Protocol.Settings.Goals.Diff.Mode.Off None) in
  let messages = DocumentManager.get_messages st None in
  let _json = Protocol.ExtProtocol.Notification.Server.ProofViewParams.yojson_of_t { proof = Some proof; messages } in
  ()

let%test_unit "goals: proof is available after error" =
  let st, init_events = init_test_doc ~text:"Lemma foo : False. easy." in
  let st, (_s1, (_s2, ())) = dm_parse st (P (P O)) in
  let st, exec_events = DocumentManager.interpret_to_end st in
  let todo = Sel.Todo.(add empty init_events) in
  let todo = Sel.Todo.(add todo exec_events) in
  let st = handle_events todo st in
  let proof = DocumentManager.get_proof st Protocol.Settings.Goals.Diff.Mode.Off None in
  [%test_eq: bool] true (Option.is_some proof)