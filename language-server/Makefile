.PHONY: coq
world: coq
	dune build coq/coq-core.install coq/coq-stdlib.install vscoq-language-server.install sel.install

coq/config/coq_config.ml:
	cd coq
	./configure -no-ask -prefix $(shell pwd)/_build/install/default/

.PHONY: coq
.coq: coq/config/coq_config.ml
