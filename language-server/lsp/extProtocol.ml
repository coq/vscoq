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
open LspData

module Notification = struct

  module Client = struct

    include Protocol.Notification.Client

    module InterpretToPointParams = struct

      type t = {
        textDocument : VersionedTextDocumentIdentifier.t;
        position : Position.t;
      } [@@deriving yojson]

    end

    module InterpretToEndParams = struct

      type t = {
        textDocument : VersionedTextDocumentIdentifier.t;
      } [@@deriving yojson]

    end

    module StepBackwardParams = struct

      type t = {
        textDocument : VersionedTextDocumentIdentifier.t;
      } [@@deriving yojson]

    end

    module StepForwardParams = struct

      type t = {
        textDocument : VersionedTextDocumentIdentifier.t;
      } [@@deriving yojson]

    end

    type t =
    | Std of Protocol.Notification.Client.t
    | InterpretToEnd of InterpretToEndParams.t
    | InterpretToPoint of InterpretToPointParams.t
    | StepForward of StepForwardParams.t
    | StepBackward of StepBackwardParams.t

    let t_of_jsonrpc (JsonRpc.Notification.{ method_; params } as notif) =
      match method_ with
      | "vscoq/interpretToPoint" -> InterpretToPoint InterpretToPointParams.(t_of_yojson params)
      | "vscoq/stepBackward" -> StepBackward StepBackwardParams.(t_of_yojson params)
      | "vscoq/stepForward" -> StepForward StepForwardParams.(t_of_yojson params)
      | "vscoq/interpretToEnd" -> InterpretToEnd InterpretToEndParams.(t_of_yojson params)
      | _ -> Std (Protocol.Notification.Client.t_of_jsonrpc notif)

  end

  module Server = struct

    include Protocol.Notification.Server

    module UpdateHighlightsParams = struct

      type t = {
        uri : Uri.t;
        parsedRange : Range.t list;
        processingRange : Range.t list;
        processedRange : Range.t list;
      } [@@deriving yojson]

    end

    module ProofViewParams = struct

      type t = Proof.data option

      let yojson_of_t pv = yojson_of_option LspEncode.mk_proofview pv

    end


    type t =
    | Std of Protocol.Notification.Server.t
    | UpdateHighlights of UpdateHighlightsParams.t
    | ProofView of ProofViewParams.t
    | SearchResult of query_result

    let jsonrpc_of_t = function
      | Std notification ->
        Protocol.Notification.Server.jsonrpc_of_t notification
      | UpdateHighlights params ->
        let method_ = "vscoq/updateHighlights" in
        let params = UpdateHighlightsParams.yojson_of_t params in
        JsonRpc.Notification.{ method_; params }
      | ProofView params -> 
        let method_ = "vscoq/proofView" in
        let params = ProofViewParams.yojson_of_t params in 
        JsonRpc.Notification.{ method_; params}
      | SearchResult params ->
        let method_ = "vscoq/searchResult" in
        let params = yojson_of_query_result params in
        JsonRpc.Notification.{ method_; params }      

    end

end

module Request = struct

  module Client = struct

  include Protocol.Request.Client

  module ResetParams = struct

    type t = {
      uri : Uri.t;
    } [@@deriving yojson]

  end

  module AboutParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t;
      pattern : string;
    } [@@deriving yojson]

  end

  module CheckParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t;
      pattern : string;
    } [@@deriving yojson]

  end

  module LocateParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t;
      pattern : string;
    } [@@deriving yojson]

  end

  module PrintParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t;
      pattern : string;
    } [@@deriving yojson]

  end

  module SearchParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t;
      pattern : string;
      id : string;
    } [@@deriving yojson]

  end

  module UpdateProofViewParams = struct

    type t = {
      textDocument : VersionedTextDocumentIdentifier.t;
      position : Position.t option;
    } [@@deriving yojson]

  end

  module UpdateProofViewResult = struct

    type t = Proof.data option

    let yojson_of_t pv = yojson_of_option LspEncode.mk_proofview pv

  end

  module DocumentStateParams = struct 

    type t = {
      textDocument : TextDocumentIdentifier.t;
    } [@@deriving yojson]

  end

  module DocumentStateResult = struct
    
    type t = {
      document : string;
    } [@@deriving yojson]

  end

  type 'rsp params =
  | UpdateProofView : UpdateProofViewParams.t -> UpdateProofViewResult.t params
  | Reset : ResetParams.t -> unit params
  | About : AboutParams.t -> string params
  | Check : CheckParams.t -> string params
  | Locate : LocateParams.t -> string params
  | Print : PrintParams.t -> string params
  | Search : SearchParams.t -> unit params
  | DocumentState : DocumentStateParams.t -> DocumentStateResult.t params 

  type t =
  | Std : int * _ Protocol.Request.Client.params -> t
  | Ext : int * _ params -> t

  let t_of_jsonrpc (JsonRpc.Request.{ id; method_; params } as req) =
    match method_ with
    | "vscoq/resetCoq" -> Ext (id, Reset ResetParams.(t_of_yojson params))
    | "vscoq/updateProofView" -> Ext (id, UpdateProofView UpdateProofViewParams.(t_of_yojson params))
    | "vscoq/search" -> Ext (id, Search SearchParams.(t_of_yojson params))
    | "vscoq/about" -> Ext (id, About AboutParams.(t_of_yojson params))
    | "vscoq/check" -> Ext (id, Check CheckParams.(t_of_yojson params))
    | "vscoq/locate" -> Ext (id, Locate LocateParams.(t_of_yojson params))
    | "vscoq/print" -> Ext (id, Print PrintParams.(t_of_yojson params))
    | "vscoq/documentState" -> Ext (id, DocumentState DocumentStateParams.(t_of_yojson params))
    | _ ->
      let Protocol.Request.Client.Pack (id, req) = Protocol.Request.Client.t_of_jsonrpc req in
      Std (id, req)

  let yojson_of_response : type a. a params -> a -> Yojson.Safe.t =
    fun req resp ->
      match req with
      | UpdateProofView _ -> UpdateProofViewResult.(yojson_of_t resp)
      | Reset _ -> yojson_of_unit resp
      | About _ -> yojson_of_string resp
      | Check _ -> yojson_of_string resp
      | Locate _ -> yojson_of_string resp
      | Print _ -> yojson_of_string resp
      | Search _ -> yojson_of_unit resp
      | DocumentState _ -> DocumentStateResult.(yojson_of_t resp)

  type 'b dispatch = {
    dispatch_std : 'a. id:int -> 'a Protocol.Request.Client.params -> ('a, string) result * 'b;
    dispatch_ext : 'a. id:int -> 'a params -> ('a, string) result * 'b;
  }

  let yojson_of_result : JsonRpc.Request.t -> 'a dispatch -> Yojson.Safe.t * 'a =
    fun req dispatch ->
      match t_of_jsonrpc req with
      | Std (id, req) ->
        let resp, data = dispatch.dispatch_std ~id req in
        let result = begin match resp with
        | Error message ->
          Error JsonRpc.Response.Error.{ code = LspData.Error.requestFailed; message }
        | Ok resp ->
          Ok (Protocol.Request.Client.yojson_of_response req resp)
        end
        in
        JsonRpc.Response.(yojson_of_t { id; result }), data
      | Ext (id, req) ->
        let resp, data = dispatch.dispatch_ext ~id req in
        let result = begin match resp with
        | Error message ->
          Error JsonRpc.Response.Error.{ code = LspData.Error.requestFailed; message }
        | Ok resp ->
          Ok (yojson_of_response req resp)
        end
        in
        JsonRpc.Response.(yojson_of_t { id; result }), data

  end

  module Server = struct

  include Protocol.Request.Server

  end

end