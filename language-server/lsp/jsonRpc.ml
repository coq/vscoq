let jsonrpc_version = `String "2.0"

module Notification = struct

type t = { method_ : string; params : Yojson.Safe.t }

let yojson_of_t { method_; params } : Yojson.Safe.t =
  `Assoc ["jsonrpc", jsonrpc_version; "method", `String method_; "params", params]

end

module Request = struct

type t = { id : int; method_ : string; params : Yojson.Safe.t }

let yojson_of_t { id; method_; params } : Yojson.Safe.t =
  `Assoc ["jsonrpc", jsonrpc_version; "id", `Int id; "method", `String method_; "params", params]

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

end