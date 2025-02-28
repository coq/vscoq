
(* TODO: put inside a mutex lock and promise return type *)

val get_proof : previous:Vernacstate.t option -> Protocol.Settings.Goals.Diff.Mode.t -> Vernacstate.t -> Protocol.ProofState.t option
val get_hover_contents :
  Environ.env ->
  Evd.evar_map ->
  Libnames.qualid Constrexpr.or_by_notation ->
  Lsp.Types.MarkupContent.t option
val is_opaque_flat_proof :
  Vernacextend.vernac_qed_type ->
  section_depth:int ->
  (Vernacextend.vernac_classification * Synterp.vernac_control_entry) list ->
    Vernacexpr.section_subset_expr option

module DelegationManager : sig
type job_handle
val cancel_job : job_handle -> unit
val mk_job_handle : Feedback.route_id * Types.sentence_id -> job_handle
end

val init_document : 'a ->  Vernacstate.t -> Vernacstate.t

type parser_result = {
  ast : Vernacexpr.vernac_control;
  loc : Loc.t;
  stop : int;
  begin_char : int;
  tokens : Tok.t list;
  comments : ((int * int) * string) list
}
type synterp_result = {
  parsed : parser_result;
  ast : Synterp.vernac_control_entry;
  classification : Vernacextend.vernac_classification;
  synterp_state : Vernacstate.Synterp.t;
}

exception Error of Loc.t option * Pp.t * Types.Quickfix.t list option
val with_err : ('a -> 'b) -> 'a -> 'b

exception ParseError of Loc.t option * Pp.t * Types.Quickfix.t list option
exception SynterpError of parser_result * Loc.t option * Pp.t * Types.Quickfix.t list option

val parse_and_synterp_one_sentence_err : 
     ?loc:Loc.t ->
      string ->
     (unit, char) Gramlib.Stream.t ->
     st:Vernacstate.Synterp.t ->
      synterp_result option
 
val junk_sentence_end : (unit, char) Gramlib.Stream.t -> unit

val init : usage:Boot.Usage.specific_usage -> Coqargs.t -> unit
val start_library : init_vs:Vernacstate.t -> path:string -> Coqargs.injection_command list -> Vernacstate.t

val jump_to_definition : Vernacstate.Synterp.t -> Vernacstate.t option -> string -> (Loc.t * string) option

val smart_global : Libnames.qualid Constrexpr.or_by_notation Pcoq.Entry.t
val lconstr : Constrexpr.constr_expr  Pcoq.Entry.t
val search_queries : ((bool * Vernacexpr.search_request) list * Libnames.qualid list Vernacexpr.search_restriction) Pcoq.Entry.t
val parse_entry : Vernacstate.Synterp.t -> 'a Pcoq.Entry.t -> string -> 'a

val print_about : Environ.env -> Evd.evar_map -> Libnames.qualid Constrexpr.or_by_notation -> UnivNames.full_name_list option -> Pp.t
val check_may_eval : Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr option -> Constrexpr.constr_expr -> Pp.t
val print_located_qualid : Environ.env -> Evd.evar_map -> Libnames.qualid Constrexpr.or_by_notation -> Pp.t
val print_name : Environ.env -> Evd.evar_map -> Libnames.qualid Constrexpr.or_by_notation -> Pp.t
module Pure : sig

val severity_of_feedback_level : Feedback.level -> Protocol.LspWrapper.DiagnosticSeverity.t
val channel_of_feedback_level : Feedback.level -> Protocol.LspWrapper.FeedbackChannel.t option
val string_of_ppcmds : Pp.t -> string
val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
val is_section_begin : Synterp.vernac_control_entry -> bool
val is_section_end : Synterp.vernac_control_entry -> bool
val pp_of_coq_pp : Pp.t -> Protocol.Printing.pp

end