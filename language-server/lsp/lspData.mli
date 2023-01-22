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
