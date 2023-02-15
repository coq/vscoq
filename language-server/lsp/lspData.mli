module Position :
  sig
    type t = { line : int; char : int; }
    val compare : t -> t -> int
    val to_string : t -> string
  end
module Range : sig type t = { start : Position.t; stop : Position.t; } end

type diagnostic = {
  range : Range.t;
  message : string;
  severity : Feedback.level;
} [@@deriving sexp]

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