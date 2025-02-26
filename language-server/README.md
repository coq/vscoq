# VSRocq Language Server

This is a language server for Rocq speaking LSP with a few additional messages
which are VSRocq specific (e.g. declaring a point of interest, printing goals).

- [vscoqtop](vscoqtop/) is a Rocq toplevel speaking LSP based on DM and SEL
- [DM](dm/) is a document manager for Rocq:
  - it holds the documents as seen by the user
  - it orchestrates their parsing, execution (checking) and interaction (eg hover)
- [Worker](rocq-worker/) wraps all Rocq APIs organizing them into
  - pure: explicit state passing, reentrant, hence thread safe
  - stateful: executed in a single worker that fulfills a promise
- [Protocol](protocol/) defines the extensions to LSP, the datatypes used and
  their json serializers
