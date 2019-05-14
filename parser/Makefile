all: parser
	./parser

lib.cmo lib.cmi: lib.ml
	ocamlc -c lib.ml

smartCalculus.cmo smartCalculus.cmi: smartCalculus.ml lib.cmi
	ocamlc -c smartCalculus.ml

parserCombinator.cmo parserCombinator.cmi: parserCombinator.ml smartCalculus.cmi
	ocamlc -c parserCombinator.ml 


parser: grammar.ml parserCombinator.cmo smartCalculus.cmo lib.cmo
	ocamlc -g -o parser unix.cma lib.cmo smartCalculus.cmo parserCombinator.cmo grammar.ml


clean:
	rm -f *.cmi *.cmo parser


