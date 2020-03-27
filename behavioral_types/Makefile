SOURCES = lib.ml microSolidity.ml parserCombinator.ml grammar.ml analyzer.ml
EXEC = analyzer
CAMLC = ocamlc -g
CAMLDEP = ocamldep
LIBS=$(WITHUNIX)
WITHUNIX =unix.cma -cclib -lunix
OBJS = $(SOURCES:.ml=.cmo)

all: depend $(EXEC)

exec: $(EXEC)
	./$(EXEC)

$(EXEC): $(OBJS)
	$(CAMLC) $(CUSTOM) -o $(EXEC) $(LIBS) $(OBJS)

.SUFFIXES:
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(CAMLC) -c $<

.mli.cmi:
	$(CAMLC) -c $<

clean:
	rm -f *.cmo *.cmi *.json $(EXEC)

depend: $(SOURCES)
	$(CAMLDEP) *.mli *.ml > .depend

include .depend
