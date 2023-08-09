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
open Sexplib.Std

module Position = struct

  include Lsp.Types.Position

  type t = [%import: Lsp.Types.Position.t] [@@deriving sexp]
 
  let compare pos1 pos2 =
    match Int.compare pos1.line pos2.line with
    | 0 -> Int.compare pos1.character pos2.character
    | x -> x

  let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.character

end

module Range = struct

  include Lsp.Types.Range

  type t = [%import: Lsp.Types.Range.t] [@@deriving sexp]

  let included ~in_ { start; end_ } =
    let (<=) x y = Position.compare x y <= 0 in
    in_.start <= start && end_ <= in_.end_

end 

module DiagnosticSeverity = struct

  type t = [%import: Lsp.Types.DiagnosticSeverity.t] [@@deriving sexp]

  let of_feedback_level = let open DiagnosticSeverity in function
    | Feedback.Error -> Some Error
    | Feedback.Warning -> Some Warning
    | Feedback.(Info | Debug | Notice) -> None

end

module FeedbackChannel = struct

  type t = 
  | Debug 
  | Info
  | Notice
  [@@deriving sexp, yojson]

  let yojson_of_t = function
  | Debug -> `Int 0
  | Info -> `Int 1
  | Notice -> `Int 2

  let t_of_feedback_level = function 
  | Feedback.Debug -> Some Debug
  | Feedback.Info -> Some Info 
  | Feedback.Notice -> Some Notice 
  | Feedback.(Error | Warning) -> None

end

module CoqFeedback = struct 

  type t = {
    range: Range.t; 
    message: string; 
    channel: FeedbackChannel.t;
  } [@@deriving sexp, yojson]
  
end

type query_result =
  { id : string;
    name : string;
    statement : string;
  } [@@deriving yojson]

type notification =
  | QueryResultNotification of query_result
