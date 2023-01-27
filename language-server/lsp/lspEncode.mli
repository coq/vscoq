open LspData

val mk_notification :
  event:string ->
  params:Yojson.Safe.t -> Yojson.Safe.t

val mk_response :
  id:int ->
  result:Yojson.Safe.t ->
  Yojson.Safe.t

val mk_loc : Position.t -> Yojson.Safe.t

val mk_range : Range.t -> Yojson.Safe.t

val mk_diagnostics : string -> diagnostic list -> Yojson.Safe.t
  
val mk_goal :
  Evd.evar_map ->
  Evar.t ->
  Yojson.Safe.t

val mk_proofview : Proof.data -> Yojson.Safe.t
