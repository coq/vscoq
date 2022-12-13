[![Actions Status](https://github.com/gares/vscoq-language-server/workflows/CI/badge.svg)](https://github.com/gares/vscoq-language-server/actions)

# VSCoq Language Server

This is a language server for Coq speaking LSP with a few additional messages
which are VSCoq specific (e.g. declaring a point of interest, printing goals).

- [SEL](sel/) is a simple event library used to handle I/O
- [DM](dm/) is a document manager for Coq with support for delegation via SEL
- [vscoqtop](vscoqtop/) is a Coq toplevel speaking LSP based on DM and SEL

### Status

This software is being actively developed and should not be used in production.

### Running

The coq and vscoq submodules point to versions which are know to work.
`make run` starts `code` with the right settings.
