Support for the [Coq Proof Assistant](https://coq.inria.fr/) in [Visual Studio Code](https://code.visualstudio.com/). The status of this plugin is very much beta and somewhat experimental.

## Instructions
1. install [Coq 8.5](https://coq.inria.fr/download)
2. install [vscode](https://code.visualstudio.com/)
3. [download this extension: vscoq-0.0.1.vsix](https://github.com/siegebell/vscoq/releases/download/0.0.1-beta.1/vscoq-0.0.1.vsix)
4. run: `code --install-extension vscoq-0.0.1.vsix`
5. *optional for Windows*: to enable interrupt computation, download [coqtopw.exe](https://github.com/siegebell/vscoq/releases/download/0.0.1-beta.1/coqtopw.exe) and add `"coqtop.wrapper": "path/to/coqtopw.exe"` to your vscode settings file.
6. start vscode (run `code`)
7. open or create a new Coq script (*.v) file

## Basic usage:
* step forward: `ctrl+shift+down` 
* step backward: `ctrl+shift+up` 
* interpret to point: `ctrl+shift+right` 
* interpret to end: `ctrl+shift+end` 
* interpret to home (and reset Coq): `ctrl+shift+home`
* interrupt computation: `ctrl+shift+~`
* *explore more commands*: `F1` and begin typing `Coq:`

## Tips
* use the [prettify-symbols-mode](https://marketplace.visualstudio.com/items?itemName=siegebell.prettify-symbols-mode) extension to support fancy notation.

## Screenshots
<img alt="Screenshot of Proof Goal" src="https://cloud.githubusercontent.com/assets/16118166/15950935/9c8537dc-2e81-11e6-9954-5eefeac23a7a.png" width="45%"/> <img alt="Screenshot of LtacProf results" src="https://cloud.githubusercontent.com/assets/16118166/15950939/a00a8e02-2e81-11e6-98c4-9425bf6ab9c9.png" width="45%"/>
