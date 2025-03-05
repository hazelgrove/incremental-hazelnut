HTML_FILE=$(shell pwd)/_build/default/bin/index.html

all: fmt build

fmt:
	refmt */*.re --in-place
	refmt */*.rei --in-place

build:
	dune build bin/main.bc.js
	dune build bin/index.html
	dune build eval/eval.re.ml

url:
	@echo "file://$(HTML_FILE)"

clean:
	dune clean

deps:
	opam install dune reason incr_dom ocaml-lsp-server

.PHONY: test distill eval
test:
	dune test

distill:
	dune build test/distill_actions.re.ml

eval:
	python3 eval/eval.py
