SOURCES = lib.ml smartCalculus.ml parserCombinator.ml grammar.ml compiler.ml pythonDeploy.ml
EXEC = compiler
CAMLC = ocamlc
CAMLDEP = ocamldep
LIBS=$(WITHUNIX)
WITHUNIX =unix.cma -cclib -lunix
OBJS = $(SOURCES:.ml=.cmo)

all: depend $(EXEC)

$(EXEC): $(OBJS)
	$(CAMLC) $(CUSTOM) -o $(EXEC) $(LIBS) $(OBJS)
	./$(EXEC)

.SUFFIXES:
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(CAMLC) -c $<

.mli.cmi:
	$(CAMLC) -c $<

clean:
	rm -f *.cmo *.cmi

depend: $(SOURCES)
	$(CAMLDEP) *.mli *.ml > .depend

include .depend
