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
open Types

[@@@warning "-27"]

let uri = Uri.make ~scheme:"file" ~path:"foo" ()

let init text = openDoc uri ~text

(* ********************************************************** *)

let %test_unit "schedule: parse error in proof step becomes skipped" =
  let st, _ = init "Lemma a : True. Proof. idtac (fun x -> x). Qed." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(E(P O)))) in
  let init, (o, (p1,()), t) = task st s4.id (Proof(S O)) in
  [%test_eq: sentence_id option] (Some s1.id) init;
  [%test_eq: sentence_id] o s1.id;
  [%test_eq: sentence_id] t s4.id;
  [%test_eq: sentence_id] p1 s2.id;
  ()


let %test_unit "schedule: no section no proof using" =
  let st, _ = init "Lemma a : True. Proof. idtac. Qed." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(P(P O)))) in
  let init, (o, (p1,(p2,())), t) = task st s4.id (Proof(S(S O))) in
  [%test_eq: sentence_id option] (Some s1.id) init;
  [%test_eq: sentence_id] o s1.id;
  [%test_eq: sentence_id] t s4.id;
  [%test_eq: sentence_id] p1 s2.id;
  [%test_eq: sentence_id] p2 s3.id;
  ()

let %test_unit "schedule: transparent lemma" =
  let st, _ = init "Lemma a : True. Proof. idtac. Defined." in
  let st, (s1, (s2, (s3, (s4, ())))) = dm_parse st (P(P(P(P O)))) in
  let init, e = task st s4.id Exec in
  [%test_eq: sentence_id option] (Some s3.id) init;
  [%test_eq: sentence_id] e s4.id;
  ()
 
let %test_unit "schedule: section with proof using" =
  let st, _ = init "Section A. Variable x : Prop. Lemma a : True. Proof. idtac. Qed." in
  let st, (s1, (s2, (s3, (s4, (s5, (s6, ())))))) = dm_parse st (P(P(P(P(P(P O)))))) in
  let init, q = task st s6.id Exec in
  [%test_eq: sentence_id option] (Some s5.id) init;
  [%test_eq: sentence_id] q s6.id;
  ()
  
let %test_unit "schedule: section closed" =
  let st, _ = init "Section A. End A. Lemma a : True. Proof. idtac. Qed." in
  let st, (s1, (s2, (s3, (s4, (s5, (s6, ())))))) = dm_parse st (P(P(P(P(P(P O)))))) in
  let init, (o, (p1,(p2,())), t) = task st s6.id (Proof(S(S O))) in
  [%test_eq: sentence_id option] (Some s3.id) init;
  [%test_eq: sentence_id] o s3.id;
  [%test_eq: sentence_id] t s6.id;
  [%test_eq: sentence_id] p1 s4.id;
  [%test_eq: sentence_id] p2 s5.id;
  ()

let %test_unit "schedule: empty proof" =
  let st, _ = init "Lemma a : True. Qed." in
  let st, (s1, (s2, ())) = dm_parse st (P(P O)) in
  let init, (o, (), t) = task st s2.id (Proof O) in
  [%test_eq: sentence_id option] (Some s1.id) init;
  [%test_eq: sentence_id] o s1.id;
  [%test_eq: sentence_id] t s2.id;
  ()
