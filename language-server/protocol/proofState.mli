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
open Settings

type proof_statement [@@deriving yojson]

type proof_step [@@deriving yojson]

type proof_block [@@deriving yojson]

type t [@@deriving yojson]

val get_proof : previous:Vernacstate.t option -> Goals.Diff.Mode.t -> Vernacstate.t -> t option

val mk_proof_statement : string -> Lsp.Types.Range.t -> proof_statement
val mk_proof_step : string -> Lsp.Types.Range.t -> proof_step
val mk_proof_block : proof_statement -> proof_step list -> Lsp.Types.Range.t -> proof_block