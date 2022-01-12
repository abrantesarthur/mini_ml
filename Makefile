OCAMLBUILD ?= ocamlbuild

.PHONY: build
build:
	$(OCAMLBUILD) miniml.byte

.PHONY: run
run: build
	./miniml.byte
