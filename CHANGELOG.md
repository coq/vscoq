## 0.3.6
* compatibility with Coq 8.15 (#264, by @quarkcool and @fakusb)
* bumped and cleaned up dependencies (#234, #263, #264 and #265 by @dependabot and @fakusb)
* fixed colorization of keywords in identifiers (#251, by @julesjacobs)
* give more informative goal message on shelved/admitted goals (#184, by @fakusb)
* fixed typos (#258 and #259, by @jacklee1792 and @j3parker)
* better documentation for coqtop.args option (#224, by @fakusb)

## 0.3.5
* compatibility with vscode 1.57.0 (#238, by @swils)
* fixed compatibility with snap (#223, by @gares and @fakusb)
* add shields to readme (#218, by @fakusb)
* typo readme (#217, by @artagnon)
* bumped dependencies to avoid vulnerabilities (#222, by @dependabot)

## 0.3.4
* added changelog from 0.3.3

## 0.3.3

* fix very narrow proof view (#170 and #173, by @fakusb)
* files can now be reentered by coq after closing (#169, by @fakusb)
* recognise more keywords (#159, #168 and #209, by @artagnon)
* improved recognition of qualified identifiers and notations for query guessing (#165 and #175, by @fakusb)
* remove snippet that interfered with `match ... with` (#160, by @artagnon)
* "Display Implicit Arguments" now indeed does display the implicit arguments (@182, by @fakusb)
* fix mangled diffs of changed terms (#172, by @fakusb)
* added option to not italicize/strikethrough diffs of changed terms (#166, by @fakusb)
* added option to select location of `_CoqProject` (#179, by @fakusb)
* proofview no longer gets put to foreground on changed (#195, by @Blaisorblade)
* fixed wrong assumption on Coq-xml protocol (#191, by @fakusb)
* clean up makefile (#178, by @artagnon)
* added build and install instructions from source to README (#145, by @thery)
* fixed debugger integration for language server (#180, by @fakusb) 
* reduced npm dependencies (#171, by @fakusb)
* deleted outdated TODO.md (#149, by @Blaisorblade)
* cleaned up readme file (#196, by @Blaisorblade)
* collapsed duplicates and modernized license files (#177, by @artagnon)
* bumped dependencies to avoid vulnerabilities (#148, #152, #174, #189 and #210, by @dependabot)

## 0.3.2
* improved indentation rules (#90, by @artagnon)
* auto-focus ProofView when its content is updated (#143, @JimmyZJX)
* more keyword highlighting (#136, by @artagnon)
* fix paths to icons representing focus (#141, by @maximedenes)
* acquire new setting for executing hoqidetop (#97, by @artagnon)
* interrupt Coq with SIGINT (#127, by @jad-hamza)
* improved position in proof view for large contexts (#130, by @thery)
* add icon (#117, by @maximedenes)
* fix `_CoqProject` parsing (#111, by @maximedenes)

## 0.3.1
* fix #74 (document desynchronized after undo) (by @maximedenes)
* Add utf8 syntax highlighting (#71, by @KyleDavidE)
* fix #76 (auto bracketting and comment) (by @GabrielaMafra)
* various improvements of the build layout (by @artagnon)

## 0.3.0
* development moved to Coq Community
* support for Coq >= 8.7.0
* drop support for Coq < 8.7.0
* update to VSCode >= 1.23.0
* simplify build system
* update dependencies to avoid vulnerabilities
* do not reset Coq when going back past the beginning of document (#29)
* remove coqtop wrapper (#31)
* do not focus info panel when info feedback is received (#35)
* make parser understand lp:{{...}} (elpi) quotations (#40)
* change default navigation keybindings (#45)
* show warnings in diagnostics (#47)
* remove company-coq submodule (#48)
* remove external opening of proof view (#49)
* replace proofview customization logic with themable colors (#54)
* change keybindings for macOS to avoid beeps (#56)
* by default, do not indent after opening a proof (#67)
* fix #14 (VsCoq's parser not coping with some notations)
* fix #18 (Debug messages are not displayed)
* fix #26 (Focus lost on first go to point)
* fix #33 (Top module name should be set properly)
* fix #39 (UnhandledPromiseRejectionWarning)
* fix #59 (Output spaces instead of non-breaking spaces)
* fix #60 (Clear the goals when not in proof mode)
* fix #65 (VsCoq does not work with Coq built using Dune)

Note: PR and issue numbers below refer to the previous VsCoq repository
(https://github.com/siegebell/vscoq).

* fix #130 (AST parsing assumptions fails)
* fix #138 (Query Results and Notices overwrite rather than append)
* fix #157 (Search doesn't appear to prove all results)

## 0.2.7
* feature: diff in error messages (#106)
* fix #105 (bad parsing of bullets, introduced by 0.2.6)

## 0.2.6
* partial resolution to #100 - allow specifying where user-settings should go. Note: this setting may be removed in the future when vscode supports this functionality.
    * setting: `coq.hacks.userSettingsLocation`
* fixes #101 #102 #103 #104 (UI & parsing)

## 0.2.5
* external view: option to host the proof-view via a webserver (#96)
    * settings: `coq.externalViewScheme`
* fixes: #96 #98 #99

## 0.2.4
* "finish computations" command (#24)
    * command: "Finish Computations" --> `extension.coq.finishComputations`
* customize proof-view theme (#91)
    * command: "Customize proof-view styling" --> `extension.coq.proofView.customizeProofViewStyle`
* better auto-indenting (#87 #88)
    * settings: `coq.editor.indentAfterBullet` 
* support custom command to externally view proof-state (#95)
    * settings: `coq.externalViewUrlCommand`
* feature: reveal cached proof state at cursor (#66)
    * settings: `coq.autoRevealProofStateAtCursor`
    * command: "View the proof-state at the cursor position" --> `extension.coq.proofView.viewStateAt`
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
