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
module TacticWorkerProcess : sig
  type options
[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
   val parse_options : string list -> options * string list
[%%else]
   val parse_options : Coqargs.t -> string list -> options * string list
[%%endif]
  val main : st:Vernacstate.t -> options -> unit
  val log : ?force:bool -> (unit -> string) -> unit
end

(* HACK: the sentence id of the current phrase is used to report errors *)
val set_id_for_feedback : Feedback.route_id -> Types.sentence_id -> unit
