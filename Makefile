all: componi
	./componi

qelim: qElim.cmo
	ocamlc -g -o qelim lib.cmo qElim.cmo

lib.cmo lib.cmi: lib.ml
	ocamlc -c lib.ml

qElim.cmo qElim.cmi: qElim.ml
	ocamlc -c qElim.ml

smartCalculus.cmo: smartCalculus.ml lib.cmi
	ocamlc -c smartCalculus.ml

componi: componi.ml lib.cmo smartCalculus.cmo qElim.cmo
	ocamlc -g -o componi unix.cma lib.cmo smartCalculus.cmo qElim.cmo componi.ml

clean:
	rm -f *.cmi *.cmo componi

.PHONY: all clean
