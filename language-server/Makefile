pwd := $(shell pwd)

build:
	dune build vscoq-language-server.install sel.install

_build/.vscode-extensions:
	git submodule update --init vscoq && cd vscoq && make
	rm -rf _build/.vscode-extensions && mkdir _build/.vscode-extensions && unzip vscoq/vscoq-0.4.0.vsix -d _build/.vscode-extensions/ && cd _build/.vscode-extensions/ && mv extension maximedenes.vscoq-0.4.0

run: build _build/.vscode-extensions
	code -n --extensions-dir $(pwd)/_build/.vscode-extensions -w tests/interactive

code:
	which node
	export COQLIB=$(pwd)/_build/default/coq/; \
	export PATH=$(pwd)/_build/install/default/bin:$$PATH; \
	eval $$(opam env); \
	code .
