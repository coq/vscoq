## 0.2.4
* "finish computations" command (#24)
* customize proof-view theme (#91)
* better auto-indenting (#87 #88)
* fix #94 #93 #92

## 0.2.0-0.2.3
* improve mac keybindings
* fix #84: _CoqProject handling (args were not being correctly filtered and passed to coqtop)
* fix #85: diff view poorly matches goals for diffing
* graceful handling of 'coqtop not found'

## 0.1.6
* Support for Coq 8.6
* LtacProfiling results view
* basic symbols/definition lookup within document
* some coloring for richpp message in proof-view
* new feature: *synchronous* interpret to point
* new option: interpretToEndOfLine

## 0.1.5
* fixed broken dependencies

## 0.1.4
* support for RichPP in the 8.6 protocol (no highlighting as of yet)
* apply prettify-symbols-mode to query results, errors, and messages
* more snippets
* parser fixes (better Unicode handling)

## 0.1.3 
* fixed prettify-symbols-mode in proof-view
* somewhat better error handling around pegjs parser errors
* redirect console to connection.console (3rd party libs were breaking the jsonrpc protoocl over console)

## 0.1.2 Lanuch vscoq server locally (don't rely on Node env path)

## 0.1.1 Fixed some hyperlinks

## 0.1.0 Initial public release