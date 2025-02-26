
(* TODO: put inside a mutex lock and promise return type *)

val get_proof : previous:Vernacstate.t option -> Protocol.Settings.Goals.Diff.Mode.t -> Vernacstate.t -> Protocol.ProofState.t option
val get_hover_contents :
  Environ.env ->
  Evd.evar_map ->
  Libnames.qualid Constrexpr.or_by_notation ->
  Lsp.Types.MarkupContent.t option

[%% if coq = "8.18" || coq = "8.19" || coq = "8.20" ]
val feedback_add_feeder_on_Message : (Feedback.route_id -> Stateid.t -> Feedback.doc_id -> Feedback.level -> Loc.t option -> 'a list -> Pp.t -> unit) -> int
[%%else]
val feedback_add_feeder_on_Message : (Feedback.route_id -> Stateid.t  -> Feedback.doc_id -> Feedback.level -> Loc.t option -> Quickfix.t list -> Pp.t -> unit) -> int
[%%endif]
val feedback_delete_feeder : int -> unit
    
module Pure : sig

val severity_of_feedback_level : Feedback.level -> Protocol.LspWrapper.DiagnosticSeverity.t
val channel_of_feedback_level : Feedback.level -> Protocol.LspWrapper.FeedbackChannel.t option
val string_of_ppcmds : Pp.t -> string
val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
 
end