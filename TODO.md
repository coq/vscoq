Basic Functionality
- [x] Track highlights **per** document
- [x] Edit causes editAt event as necessary
- [x] Allow whitespace and comment editing of interpreted text
- [x] Edit_at when editing an interpreted proof (and not whitespace)
- [x] Go to point
- [x] Clear all highlights upon reset
- [x] stack of currentTip
- [x] show Goal and Hyps
- [~] interrupt computation (Windows for now, expose console where user can type ctrl+break)
- [ ] edit locks (ensure sentence and highlight ranges are only updated in sync with coqtop interactions
- [x] implement cool mutex with cancellation tokens and global cancellation
- [ ] test fancy mutex
- [ ] mutex: chain global cancellations
- [ ] set coq options
- [ ] support queries
- [x] status bar (ready vs working)
- [x] parse bullets
- [x] forward messages to extension
- [x] display `Check` messages, etc.
- [ ] quotes in comments must be correctly matched
- [ ] quotes in comments must be correctly matched for syntax highlighting
- [ ] handle _CoqProject
- [ ] syntax coloring (not as a separate package)
- [x] lazy load coqtop
- [ ] show info messages in own output buffer
- [ ] editAt + insert text seems to break highlighting
- [ ] command: finish computation
- [ ] gutter icons for each edit position
- [ ] move cursor with stepForward, etc.

Future Features
- [ ] universal RPC
- [ ] Autocompletion
- [ ] Ltac debugging
- [ ] Substitution
- [ ] Symbols (subst. for text)
- [ ] Show fancy window pane for goal and hyps, etc.
- [ ] Find references
- [ ] Find definition
- [ ] Peek definition
- [ ] Set options


