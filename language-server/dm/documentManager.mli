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

open Types
open Lsp.Types
open Protocol
open Protocol.LspWrapper
open Protocol.Printing
open CompletionItems

(** The document manager holds the view that Coq has of the currently open
    states. It makes it easy for IDEs to handle text edits, navigate
    and get feedback. Note that it does not require IDEs to parse vernacular
    sentences. *)

type observe_id = Id of Types.sentence_id | Top

type blocking_error = {
  last_range: Range.t;
  error_range: Range.t
}

type state

type event
val pp_event : Format.formatter -> event -> unit

type events = event Sel.Event.t list

val init : Vernacstate.t -> opts:Coqargs.injection_command list -> DocumentUri.t -> text:string -> observe_id option -> state * events
(** [init st opts uri text] initializes the document manager with initial vernac state
    [st] on which command line opts will be set. [background] indicates if the document should
    be executed in the background once it is parsed. *)

val apply_text_edits : state -> text_edit list -> state * events
(** [apply_text_edits doc edits] updates the text of [doc] with [edits]. 
    A ParseEvent is triggered, once processed: the new
    document is parsed, outdated executions states are invalidated, and the observe
    id is updated. Finally if [background] is set to true, an execution is launched in
    the background *)

val clear_observe_id : state -> state
(** [clear_observe_id state] updates the state to make the observe_id None *)

val reset_to_top : state -> state
(** [reset_to_top state] updates the state to make the observe_id Top *)

val get_next_range : state -> Position.t -> Range.t option
(** [get_next_range st pos] get the range of the next sentence relative to pos *)

val get_previous_range : state -> Position.t -> Range.t option
(** [get_previous_pos st pos] get the range of the previous sentence relative to pos *)

val interpret_to_position : state -> Position.t -> (state * events * blocking_error option)
(** [interpret_to_position state pos should_block] navigates to the 
    last sentence ending before or at [pos] and returns the resulting state, events that need to take place, and a possible blocking error. *)

val interpret_to_next_position : state -> Position.t -> (state * events * blocking_error option * Position.t)
(** [interpret_to_next_position state pos should_block] navigates 
    to the first sentence after or at [pos] (excluding whitespace) and returns the resulting state, events that need to take place, a possible blocking error, and the position of the sentence that was interpreted until. *)

val interpret_to_previous : state -> (state * events * blocking_error option)
(** [interpret_to_previous doc] navigates to the previous sentence in [doc]
    and returns the resulting state. *)

val interpret_to_next : state -> (state * events * blocking_error option)
(** [interpret_to_next doc] navigates to the next sentence in [doc]
    and returns the resulting state. *)

val interpret_to_end : state -> (state * events * blocking_error option)
(** [interpret_to_end doc] navigates to the last sentence in [doc]
    and returns the resulting state. *)

val interpret_in_background : state -> should_block_on_error:bool -> (state * events * blocking_error option)
(** [interpret_in_background doc] same as [interpret_to_end] but computation 
    is done in background (with lower priority) *)

val reset : state -> state * events 
(** resets Coq *)

val executed_ranges : state -> exec_overview
(** returns the ranges corresponding to the sentences
    that have been executed and remotely executes *)

val observe_id_range : state -> Range.t option
(** returns the range of the sentence referenced by observe_id **)

val get_messages : state -> Position.t option -> (DiagnosticSeverity.t * pp) list
(** returns the messages associated to a given position *)

val get_info_messages : state -> Position.t option -> (DiagnosticSeverity.t * pp) list
(** returns the Feedback.Info level messages associated to a given position *)

val get_document_symbols : state -> DocumentSymbol.t list

val all_diagnostics : state -> Diagnostic.t list
(** all_diagnostics [doc] returns the diagnostics corresponding to the sentences
    that have been executed in [doc]. *)

val get_proof : state -> Settings.Goals.Diff.Mode.t -> Position.t option -> ProofState.t option

val get_completions : state -> Position.t -> (completion_item list, string) Result.t

val handle_event : event -> state -> bool -> bool -> (state option * events * blocking_error option * bool)
(** handles events and returns a new state if it was updated. On top of the next events, it also returns info
    on whether execution has halted due to an error and returns a boolean flag stating whether the view
    should be updated *)

val search : state -> id:string -> Position.t -> string -> notification Sel.Event.t list

val about : state -> Position.t -> pattern:string -> (pp,string) Result.t

val hover : state -> Position.t -> MarkupContent.t option
(** Returns an optional Result:
    if None, the position did not have a word,
    if Some, an Ok/Error result is returned. *)

val check : state -> Position.t -> pattern:string -> (pp,string) Result.t

val locate : state -> Position.t -> pattern:string -> (pp, string) Result.t

val print : state -> Position.t -> pattern:string -> (pp, string) Result.t


module Internal : sig

  val document : state -> Document.document
  val raw_document : state -> RawDocument.t
  val execution_state : state -> ExecutionManager.state
  val string_of_state : state -> string
  val observe_id : state -> sentence_id option

  (* val validate_document : state -> state
  (** [validate_document doc] reparses the text of [doc] and invalidates the
      states impacted by the diff with the previously validated content. If the
      text of [doc] has not changed since the last call to [validate_document], it
      has no effect. *) *)


end
