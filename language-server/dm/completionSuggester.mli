val get_completion_items : DocumentManager.state -> Lsp.LspData.Position.t -> Lsp.LspData.RankingAlgoritm.t -> (float * float) -> ((string * string * string * string) list, string) Result.t
