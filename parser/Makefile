all: compiler 
	./compiler

lib.cmo lib.cmi: lib.ml
	ocamlc -c lib.ml

smartCalculus.cmo smartCalculus.cmi: smartCalculus.ml lib.cmi
	ocamlc -c smartCalculus.ml

parserCombinator.cmo parserCombinator.cmi: parserCombinator.ml smartCalculus.cmi
	ocamlc -c parserCombinator.ml 

grammar.cmo grammar.cmi: grammar.ml grammar.cmi smartCalculus.cmi parserCombinator.cmi
	ocamlc -c grammar.ml

compiler: compiler.ml grammar.cmo smartCalculus.cmo parserCombinator.cmo lib.cmo
	ocamlc -g -o compiler unix.cma lib.cmo smartCalculus.cmo parserCombinator.cmo grammar.cmo compiler.ml

clean:
	rm -f *.cmi *.cmo compiler


