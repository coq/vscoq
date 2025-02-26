[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
  module Quickfix = struct
    type t = unit
    let from_exception _ = Ok([])
    let pp = Pp.mt
    let loc _ = Loc.make_loc (0,0)
  end
[%%endif]


module Vernacstate = struct
  type t = Vernacstate.t
end

module Pp = struct
  type t = Pp.t
end

module Stateid = struct
  type t = Stateid.t
  let compare = Stateid.compare
  module Set : Set.S with type elt = t = Stateid.Set
end

module CMap : module type of CMap = CMap

module Loc = struct
  type t = Loc.t = {
    fname : Loc.source;
    line_nb : int;
    bol_pos : int;
    line_nb_last : int;
    bol_pos_last : int;
    bp : int;
    ep : int;
  }
end

