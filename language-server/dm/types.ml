open Lsp.LspData

type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t
type ast = Synterp.vernac_entry_control

type text_edit = Range.t * string

let initial_synterp_state = Summary.empty_frozen
