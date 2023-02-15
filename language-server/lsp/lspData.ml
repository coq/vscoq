open Sexplib.Std

module Position = struct
  
  type t = { line : int; char : int; } [@@deriving sexp]

  let compare pos1 pos2 =
    match Int.compare pos1.line pos2.line with
    | 0 -> Int.compare pos1.char pos2.char
    | x -> x

  let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.char

end

module Range = struct
  type t = { start : Position.t; stop : Position.t; } [@@deriving sexp]
end 

type diagnostic = {
  range : Range.t;
  message : string;
  severity : (Feedback.level [@sexp.opaque]);
} [@@deriving sexp]

type query_result =
  { id : string;
    name : string;
    statement : string;
  } [@@deriving yojson]

type notification =
  | QueryResultNotification of query_result

module Error = struct
  let parseError = -32700
	let invalidRequest = -32600
	let methodNotFound = -32601
	let invalidParams = -32602
	let internalError = -32603
	let jsonrpcReservedErrorRangeStart = -32099
	let serverNotInitialized = -32002
	let unknownErrorCode = -32001
	let lspReservedErrorRangeStart = -32899
	let requestFailed = -32803
	let serverCancelled = -32802
	let contentModified = -32801
	let requestCancelled = -32800
	let lspReservedErrorRangeEnd = -32800

end