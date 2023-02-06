val mk_goal :
  Evd.evar_map ->
  Evar.t ->
  Yojson.Safe.t

val mk_proofview : Proof.data -> Yojson.Safe.t
