module TacticWorkerProcess : sig
  type options
  val parse_options : string list -> options * string list
  val main : st:Vernacstate.t -> options -> unit
  val log : string -> unit
end

(* HACK: the sentence id of the current phrase is used to report errors *)
val set_id_for_feedback : Stateid.t -> unit
