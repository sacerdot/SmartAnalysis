all: componi
	./componi

componi: componi.ml
	ocamlc -g -o componi unix.cma componi.ml

.PHONY: all
