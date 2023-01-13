open LspData

val mk_notification :
  event:string ->
  params:Yojson.Basic.t -> Yojson.Basic.t

val mk_response :
  id:int ->
  result:Yojson.Basic.t ->
  Yojson.Basic.t

val mk_loc : Position.t -> Yojson.Basic.t

val mk_range : Range.t -> Yojson.Basic.t

val mk_diagnostics : string -> diagnostic list -> Yojson.Basic.t
  
val mk_goal :
  Evd.evar_map ->
  Evar.t ->
  Yojson.Basic.t

val mk_proofview : Proof.data -> Yojson.Basic.t
