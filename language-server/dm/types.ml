open Lsp.LspData

type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t
type ast = Vernacexpr.vernac_control

type text_edit = Range.t * string

