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
module Position :
  sig
    type t = { line : int; character : int; } [@@deriving yojson]
    val compare : t -> t -> int
    val to_string : t -> string
  end

module Range : sig
  type t = { start : Position.t; end_ : Position.t; } [@@deriving yojson]
end

module CompletionItem : sig 
  (* More properties exist, but we only use these currently *)
  (* See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_completion *)
  type t = {
    label : string;
    insertText : string option;
    detail : string option;
    documentation : string option;
    sortText : string option;
  } [@@deriving yojson]
end

module CompletionList : sig 
  type t = {
    isIncomplete : bool;
    items : CompletionItem.t list;
  } [@@deriving yojson]
end

module Severity : sig

  type t = Feedback.level =
  | Debug
  | Info
  | Notice
  | Warning
  | Error
  [@@deriving sexp, yojson]

end

module Diagnostic : sig

  type t = {
    range : Range.t;
    message : string;
    severity : Severity.t;
  } [@@deriving sexp, yojson]

end

type query_result =
  { id : string;
    name : string;
    statement : string;
  } [@@deriving yojson]

type notification =
  | QueryResultNotification of query_result

module Error : sig
  val parseError : int
  val invalidRequest : int
  val methodNotFound : int
  val invalidParams : int
  val internalError : int
  val jsonrpcReservedErrorRangeStart : int
  val serverNotInitialized : int
  val unknownErrorCode : int
  val lspReservedErrorRangeStart : int
  val requestFailed : int
  val serverCancelled : int
  val contentModified : int
  val requestCancelled : int
  val lspReservedErrorRangeEnd : int
end

module ServerCapabilities : sig

  type textDocumentSyncKind =
  | None
  | Full
  | Incremental
  [@@deriving yojson]

  type completionItem = {
    labelDetailsSupport : bool option;
  } [@@deriving yojson]

  type completionOptions = {
    triggerCharacters : string list option;
    allCommitCharacters : string list option;
    resolveProvider : bool option;
    completionItem : completionItem option;
  } [@@deriving yojson]

  type t = {
    textDocumentSync : textDocumentSyncKind;
    completionProvider : completionOptions;
    hoverProvider : bool;
  } [@@deriving yojson]

end

module ServerInfo : sig

    type t = {
      name: string; 
      version: string; 
    } [@@deriving yojson]

end

module InitializeResult : sig
  
  type t = {
    capabilities: ServerCapabilities.t; 
    serverInfo: ServerInfo.t;
  } [@@deriving yojson]

end

module Hover : sig
    
    type t = {
      contents: string
    } [@@deriving yojson]
  
end

module ConfigurationItem : sig

  type t = {
	  scopeUri: string option;
	  section: string option;
  } [@@deriving yojson]

end

module ConfigurationParams : sig

  type t = { items: ConfigurationItem.t list } [@@deriving yojson]

end

module Settings : sig

    module DelegationMode : sig
    type t = 
      | None
      | Skip 
      | Delegate 
      [@@deriving yojson]
    end 

    module Mode : sig

        type t =
        | Continuous 
        | Manual
        [@@deriving yojson]
    
    end

    module Proof : sig
  
      type t = {
        delegation: DelegationMode.t;
        workers: int option;
        mode: Mode.t;
      } [@@deriving yojson] [@@yojson.allow_extra_fields]
    
    end

    module RankingAlgoritm : sig
      type t = 
      | SimpleTypeIntersection
      | SplitTypeIntersection
      | StructuredTypeEvaluation
      | SelectiveUnification
      | SelectiveSplitUnification
      [@@deriving yojson]
    end
  
    type t = {
      proof: Proof.t;
      ranking: RankingAlgoritm.t;
    } [@@deriving yojson] [@@yojson.allow_extra_fields]

  
end

  