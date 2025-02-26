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

open Lsp.Types
open Printing

type proof_statement = {
  statement: string;
  range: Range.t;
} [@@deriving yojson]

type proof_step = {
  tactic: string;
  range: Range.t;
} [@@deriving yojson]

type proof_block = {
  statement: proof_statement;
  range: Range.t;
  steps: proof_step list;
} [@@deriving yojson]

type goal = {
  id: int;
  hypotheses: pp list;
  goal: pp;
} [@@deriving yojson]

type t = {
  goals: goal list;
  shelvedGoals: goal list;
  givenUpGoals: goal list;
  unfocusedGoals: goal list;
} [@@deriving yojson]

val mk_proof_statement : string -> Lsp.Types.Range.t -> proof_statement
val mk_proof_step : string -> Lsp.Types.Range.t -> proof_step
val mk_proof_block : proof_statement -> proof_step list -> Lsp.Types.Range.t -> proof_block