[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
module Quickfix = struct
  type t = unit
  let from_exception _ = Ok([])
  let pp = Pp.mt
  let loc _ = Loc.make_loc (0,0)
end
[%%else]
module Quickfix = Quickfix
[%%endif]


module Vernacstate = struct
  type t = Vernacstate.t
  module Synterp = struct
    type t = Vernacstate.Synterp.t
  end
  let synterp_st_of_vs (x : Vernacstate.t) : Synterp.t = x.Vernacstate.synterp
end

module Names = struct
  module Id = struct
    type t = Names.Id.t
    let to_string = Names.Id.to_string
  end

end

module Vernacextend = struct

  type vernac_start = Vernacextend.opacity_guarantee * Names.Id.t list
  type vernac_sideff_type = Names.Id.t list * Vernacextend.vernac_when
  type vernac_classification = Vernacextend.vernac_classification =
  | VtStartProof of vernac_start
  | VtSideff of vernac_sideff_type
  | VtQed of Vernacextend.vernac_qed_type
  | VtProofStep of { proof_block_detection : string option }
  | VtQuery
  | VtProofMode of Pvernac.proof_mode
  | VtMeta
end

module Synterp = struct
  type vernac_control_entry = Synterp.vernac_control_entry

  type outline_type =
    | Theorem
    | Definition
    | Inductive
    | Other

  let outline_entry_of (x : vernac_control_entry) : outline_type option =
    match x.v.expr with
    | VernacSynterp (Synterp.EVernacExtend _) -> Some Other
    | VernacSynterp _ -> None
    | VernacSynPure pure -> 
      match pure with
      | Vernacexpr.VernacStartTheoremProof _ -> Some Theorem
      | Vernacexpr.VernacDefinition _ -> Some Definition
      | Vernacexpr.VernacFixpoint _ -> Some Definition
      | Vernacexpr.VernacCoFixpoint _ -> Some Definition
      | _ -> None

end

module Vernacexpr = struct
  type section_subset_expr = Vernacexpr.section_subset_expr
  type inductive_kind = Vernacexpr.inductive_kind
end

module Decls = struct
  type theorem_kind = Decls.theorem_kind
  type definition_object_kind = Decls.definition_object_kind
end

module Stream = struct
  type ('a,'b) t = ('a,'b) Gramlib.Stream.t
  let count = Gramlib.Stream.count
  let of_string = Gramlib.Stream.of_string
  let junk = Gramlib.Stream.junk
end

module Tok = struct
  type t = Tok.t
  let extract_string = Tok.extract_string
  let tok_equal t1 t2 =
    let open Tok in
    match t1, t2 with
    | KEYWORD s1, KEYWORD s2 -> CString.equal s1 s2
    | IDENT s1, IDENT s2 -> CString.equal s1 s2
    | FIELD s1, FIELD s2 -> CString.equal s1 s2
    | NUMBER n1, NUMBER n2 -> NumTok.Unsigned.equal n1 n2
    | STRING s1, STRING s2 -> CString.equal s1 s2
    | LEFTQMARK, LEFTQMARK -> true
    | BULLET s1, BULLET s2 -> CString.equal s1 s2
    | EOI, EOI -> true
    | QUOTATION(s1,t1), QUOTATION(s2,t2) -> CString.equal s1 s2 && CString.equal t1 t2
    | _ -> false
  let same_tokens l1 l2 = CList.equal tok_equal l1 l2
end

module Coqargs = struct
  type injection_command = Coqargs.injection_command
end

module Pp = struct
  type t = Pp.t
  let str = Pp.str
  let (++) = Pp.(++)
end

module Stateid = struct
  type t = Stateid.t
  let to_string = Stateid.to_string
  let print = Stateid.print
  let compare = Stateid.compare
  let equal = Stateid.equal
  let fresh = Stateid.fresh
  
  module Set : Set.S with type elt = t = Stateid.Set
end

type sentence_id = Stateid.t

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
  type 'a located = t option * 'a
end

module CErrors = struct
  let anomaly = CErrors.anomaly
end

module CList = struct
  let uniquize = CList.uniquize
end

