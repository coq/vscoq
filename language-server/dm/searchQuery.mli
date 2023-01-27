open Lsp.LspData

val query_feedback : notification Sel.event

val interp_search :
  id:string ->
  Environ.env ->
  Evd.evar_map ->
  Vernacexpr.searchable -> Vernacexpr.search_restriction -> notification Sel.event list
