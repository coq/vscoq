[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[travis-shield]: https://travis-ci.com/coq-community/vscoq.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/vscoq/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237662-VsCoq-devs.20.26.20users

VsCoq is an extension for [Visual Studio
Code](https://code.visualstudio.com/) with support for the [Coq Proof
Assistant](https://coq.inria.fr/).

This extension is currently developped by @maximedenes and contributors, as
part of [Coq Community](https://github.com/coq-community/manifesto). The
original author of this extension is @siegebell.

## Features
* Asynchronous proofs
* Syntax highlighting
* Commands: step forward, interpret to point, interrupt computation, queries, set display options, etc.
* Diff view for proof-view: highlight which terms change between states
* Smarter editing: does not roll back the state when editing whitespace or comments
* Works with [prettify-symbols-mode](https://marketplace.visualstudio.com/items?itemName=siegebell.prettify-symbols-mode)
* Supports \_CoqProject
* LtacProf results treeview

## Requirements
* VsCode 1.30.0 or more recent
* Coq 8.7.0 or more recent

## Installation
The recommended way to install VsCoq is via the [Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).

## Screenshots
![vscoq](https://user-images.githubusercontent.com/647105/64025392-dbf12100-cb3c-11e9-8e7f-5c63296500f9.png)

## Instructions
1. install [Coq](https://coq.inria.fr/download)
2. install [vscode](https://code.visualstudio.com/)
3. run `code`
4. install this extension: press `F1` to open the command palette, start typing "Extensions: Install Extension", press `enter`, and search for `vscoq`
5. select "enable" on the extension

## Basic usage
* if you use _CoqProject - start vscode via `code my/project/root` (or `code .` from the root folder of your project), or else select File|Open Folder... from vscode's menu.
* step forward: `alt+down`
* step backward: `alt+up`
* interpret to point: `alt+right`
* interpret to end: `alt+end`
* interpret to home: `alt+home`
* *explore more commands*: `F1` and begin typing `Coq:`
* [vscode documentation](https://code.visualstudio.com/docs/editor/codebasics)

## Settings
(Press `F1` and start typing "settings" to open either workspace/project or user settings.)
* `"coqtop.binPath": ""` -- specify the path to coqtop (e.g. "path/to/coq/bin/")
* `"coqtop.args": []` -- an array of strings specifying additional command line arguments for coqtop
* `"coqtop.loadCoqProject": true` -- set to `false` to ignore <span>_CoqProject</span>
* `"coqtop.coqProjectRoot": "."` -- where to expect the <span>_CoqProject</span> relative to the workspace root

## Install a local version

Checkout the repo, run make, and install the produced .vsix file in the repository root by following https://code.visualstudio.com/docs/editor/extension-gallery#_install-from-a-vsix. So, either "Cmd-Shift-P" and "Extensions: Install from VSIX", or running code --install-extension vscoq-0.3.2.vsix (or whatever version number) from the terminal.

