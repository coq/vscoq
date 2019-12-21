[![Build Status](https://travis-ci.com/coq-community/vscoq.svg?branch=master)](https://travis-ci.com/coq-community/vscoq) [![Join the chat at https://gitter.im/coq-community/vscoq](https://badges.gitter.im/coq-community/vscoq.svg)](https://gitter.im/coq-community/vscoq?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

VsCoq is an extension for [Visual Studio
Code](https://code.visualstudio.com/) with support for the [Coq Proof
Assistant](https://coq.inria.fr/).

This extension is currently developped by @maximedenes and contributors, as
part of [Coq Community](https://github.com/coq-community/manifesto). The
original author of this extension is @siegebell.

## Keybindings

<kbd>F3</kbd>: Print identifier at point<br/>
<kbd>F4</kbd>: About identifier at point<br/>
<kbd>F5</kbd>: Execute until the cursor position<br/>
<kbd>F6</kbd>: Step forward<br/>
<kbd>F7</kbd>: Step backward<br/>
<kbd>F8</kbd>: Execute until end-of-file or error<br/>
<kbd>F9</kbd>: Interrupt current process

## Features

- Asynchronous proofs
- Syntax highlighting
- Commands: step forward, interpret to point, interrupt computation, queries, set display options, etc.
- Diff view for proof-view: highlight which terms change between states
- Smarter editing: does not roll back the state when editing whitespace or comments
- Works with [prettify-symbols-mode](https://marketplace.visualstudio.com/items?itemName=siegebell.prettify-symbols-mode)
- Supports \_CoqProject
- LtacProf results treeview

## Requirements

- VsCode 1.42.0 or more recent
- Coq 8.10.0 or more recent

## Installation

The recommended way to install VsCoq is via the [Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).

## Screenshots

![vscoq](https://user-images.githubusercontent.com/647105/64025392-dbf12100-cb3c-11e9-8e7f-5c63296500f9.png)
