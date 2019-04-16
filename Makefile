all: componi
	./componi

lib.cmo lib.cmi: lib.ml
	ocamlc -c lib.ml

smartCalculus.cmo: smartCalculus.ml lib.cmi
	ocamlc -c smartCalculus.ml

componi: componi.ml lib.cmo smartCalculus.cmo
	ocamlc -g -o componi unix.cma lib.cmo smartCalculus.cmo componi.ml

clean:
	rm -f *.cmi *.cmo componi

.PHONY: all clean
