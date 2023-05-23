let jsonrpc_version = `String "2.0"

module Notification = struct

type t = { method_ : string; params : Yojson.Safe.t }

let yojson_of_t { method_; params } : Yojson.Safe.t =
  `Assoc ["jsonrpc", jsonrpc_version; "method", `String method_; "params", params]

let t_of_yojson json =
  let open Yojson.Safe.Util in
  let method_ = json |> member "method" |> to_string in
  let params = json |> member "params" in
  { method_; params }

end

module Request = struct

type t = { id : int; method_ : string; params : Yojson.Safe.t }

let yojson_of_t { id; method_; params } : Yojson.Safe.t =
  `Assoc ["jsonrpc", jsonrpc_version; "id", `Int id; "method", `String method_; "params", params]

let t_of_yojson json =
  let open Yojson.Safe.Util in
  let id = json |> member "id" |> to_int in
  let method_ = json |> member "method" |> to_string in
  let params = json |> member "params" in
  { id; method_; params }

end

module Response = struct

module Error = struct

  type t = { code : int; message : string } [@@deriving yojson]

end

type t = { id : int; result : (Yojson.Safe.t, Error.t) Result.t }

let yojson_of_t { id; result } : Yojson.Safe.t =
  match result with
  | Ok json ->
    `Assoc ["jsonrpc", jsonrpc_version; "id", `Int id; "result", json]
  | Error error ->
    `Assoc ["jsonrpc", jsonrpc_version; "id", `Int id; "error", Error.yojson_of_t error]

let t_of_yojson json =
  let open Yojson.Safe.Util in
  let id = json |> member "id" |> to_int in
  let oerror = json |> member "error" |> to_option Error.t_of_yojson in
  match oerror with
  | Some error -> { id; result = Error(error) }
  | None -> { id; result = Ok(json |> member "result") }

end

type t =
  | Notification of Notification.t
  | Request of Request.t
  | Response of Response.t

let t_of_yojson json =
  let open Yojson.Safe.Util in
  let id = json |> member "id" |> to_int_option in
  if Option.is_empty id then Notification (Notification.t_of_yojson json)
  else
    let method_ = json |> member "method" |> to_string_option in
    if Option.is_empty method_ then Response (Response.t_of_yojson json)
    else Request (Request.t_of_yojson json)

let yojson_of_t = function
  | Notification notif -> Notification.yojson_of_t notif
  | Request req -> Request.yojson_of_t req
  | Response resp -> Response.yojson_of_t resp