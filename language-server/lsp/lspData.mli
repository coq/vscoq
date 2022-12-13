module Position :
  sig
    type t = { line : int; character : int; } [@@deriving yojson]
    val compare : t -> t -> int
    val to_string : t -> string
  end

module Range : sig
  type t = { start : Position.t; end_ : Position.t; } [@@deriving yojson]
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
  val requestFailed : int
end