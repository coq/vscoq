### Language Server

The module [lspManager](lspManager.mli) implements the main SEL event `lsp`
which deals with LSP requests plus some VSCoq specific messages.

[vscoqtop](vscoqtop.ml) is a Coq toplevel that initializes Coq and then runs
a SEL loop for the `lsp` event.

