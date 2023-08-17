[![CI][action-shield]][action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[action-shield]: https://github.com/coq-community/vscoq/actions/workflows/ci.yml/badge.svg?branch=main
[action-link]: https://github.com/coq-community/vscoq/actions?query=workflow:ci

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237662-VsCoq-devs.20.26.20users

VsCoq is an extension for [Visual Studio Code](https://code.visualstudio.com/)
(VS Code) and [VSCodium](https://vscodium.com/) with support for the [Coq Proof
Assistant](https://coq.inria.fr/).

This extension is currently developed and maintained as part of
[Coq Community](https://github.com/coq-community/manifesto) by
[Maxime Dénès](https://github.com/maximedenes),
[Paolo G. Giarrusso](https://github.com/Blaisorblade),
[Huỳnh Trần Khanh](https://github.com/huynhtrankhanh),
[Enrico Tassi](https://github.com/gares),
[Romain Tetley](https://github.com/rtetley),
[Laurent Théry](https://github.com/thery),
and contributors.

## Status

- VsCoq 1 (versions 0.x.y) is based on the original VsCoq implementation by [C.J. Bell](https://github.com/siegebell)
  and compatible with Coq 8.7 or more recent. It uses the legacy XML protocol
  spoken by CoqIDE. For more information, see the
  [VsCoq 1 branch](https://github.com/coq-community/vscoq/tree/vscoq1).
- VsCoq 2 (beta releases versions 1.9.x) is a full reimplementation around a
  language server which natively speaks the LSP protocol. VsCoq 2 is
  compatible with Coq 8.18 or more recent, and supports manual or continuous mode
  checking.

## Features
* Syntax highlighting
* Asynchronous proof checking
* Continuous and incremental checking of Coq documents

The new version of vscoq allows for continuous checking, see the goal panel update as you scroll or edit your document.
![](gif/continuous-mode.gif)

Note that users can opt out and choose to use the classic step by step checking mode. 
![](gif/manual-mode.gif)

* Customisable goal panel 
  
Users can choose their preferred display mode, see goals in accordion lists...
![](gif/goals-accordion.gif)

... Or organized in tabs. 
![](gif/goals-tab.gif)

* Dedicated panel for queries and their history

We now support a dedicated panel for queries. We currently support Search, Check, About, Locate and Print with plans 
to add more in the future.
![](gif/query-panel.gif)

* Supports \_CoqProject

## Installation

In order to use VsCoq 2, you will need to install both the VS Code (or VSCodium) extension and the language server.

### Requirements
* VS Code or VSCodium 1.74.0, or more recent
* Coq 8.18 or more recent. If you wish to use VsCoq with older Coq versions, please have a look at the
[VsCoq 1 branch](https://github.com/coq-community/vscoq/tree/vscoq1).

### Language server installation

The VsCoq 2 language server is currently published as a beta version on the `extra-dev` Coq OPAM repository. The recommended way to install it is through OPAM, by running :

```
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install vscoq-language-server
```

Note: VsCoq 2 currently requires Coq 8.18+rc1 as a dependency.

### Extension installation

The recommended way to install VsCoq is via the [Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) or [Open VSX](https://open-vsx.org/extension/maximedenes/vscoq).

### Settings
After installation and activation of the extension:

(Press `F1` and start typing "settings" to open either workspace/project or user settings.)
* `"vscoq.path": ""` -- specify the path to `vscoqtop` (e.g. `path/to/vscoq/bin/vscoqtop`)
* `"vscoq.args": []` -- an array of strings specifying additional command line arguments for `vscoqtop` (typically accepts the same flags as `coqtop`)

## License
Unless mentioned otherwise, files in this repository are [distributed under the MIT License](LICENSE).

The files `client/syntax/coq.tmLanguage` and `client/coq.configuration.json` are
also distributed under the MIT License, Copyright (c) Christian J. Bell and
contributors.