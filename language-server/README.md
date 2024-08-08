# VSCoq Language Server

This is a language server for Coq speaking LSP with a few additional messages
which are VSCoq specific (e.g. declaring a point of interest, printing goals).

- [SEL](sel/) is a simple event library used to handle I/O
- [DM](dm/) is a document manager for Coq with support for delegation via SEL
- [vscoqtop](vscoqtop/) is a Coq toplevel speaking LSP based on DM and SEL
