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

open Printing
open Lsp.Types

open Ppx_yojson_conv_lib.Yojson_conv.Primitives

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

let mk_proof_statement statement range = {statement; range}

let mk_proof_step tactic range = {tactic; range}

let mk_proof_block statement steps range = {steps; statement; range}