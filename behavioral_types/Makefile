C_SOURCES = utils.ml microSolidity.ml cofloco.ml solidity.ml parserCombinators.ml parser.ml compiler.ml pythonDeploy.ml pyTest.ml solidity_test.ml
C_EXEC = compiler_test

S_ANALYZER = utils.ml microSolidity.ml types.ml parserCombinators.ml parser.ml static.ml cofloco.ml typeInference.ml costEquationsGeneration.ml staticAnalyzer.ml staticAnalyzer_test.ml
S_EXEC = staticAnalyzer_test

CAMLC = ocamlc -g
CAMLDEP = ocamldep
CAMLFIND = ocamlfind

C_LIBS=$(WITHUNIX) $(WITHINTEGERS)
WITHINTEGERS =integers.cma -cclib -lintegers
WITHUNIX =unix.cma -cclib -lunix
WITH_PKGs =-package integers -package unix

C_OBJS = $(C_SOURCES:.ml=.cmo)
S_OBJS = $(S_ANALYZER:.ml=.cmo)

all: c_depend $(C_EXEC) a_depend $(S_EXEC)

$(C_EXEC): $(C_OBJS)
	$(CAMLFIND) $(CAMLC) $(WITH_PKGs) -o $(C_EXEC) $(C_LIBS) $(C_OBJS)
	./$(C_EXEC)

$(S_EXEC): $(S_OBJS)
	$(CAMLFIND) $(CAMLC) $(WITH_PKGs) -o $(S_EXEC) $(C_LIBS) $(S_OBJS)
	./$(S_EXEC)

.SUFFIXES:
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(CAMLFIND) $(CAMLC) -c $(WITH_PKGs) $<

.mli.cmi:
	$(CAMLC) -c $<

clean:
	rm -f *.cmo *.cmi *.json $(C_EXEC)

c_depend: $(C_SOURCES)
	$(CAMLDEP) *.mli *.ml > .depend_compiler

a_depend: $(S_ANALYZER)
	$(CAMLDEP) *.mli *.ml > .depend_analyzer

include .depend_compiler
include .depend_analyzer
#
#SOURCES = lib.ml microSolidity.ml parserCombinator.ml grammar.ml analyzer.ml
#EXEC = analyzer
#CAMLC = ocamlc -g
#CAMLDEP = ocamldep
#LIBS=$(WITHUNIX)
#WITHUNIX =unix.cma -cclib -lunix
#OBJS = $(SOURCES:.ml=.cmo)
#
#all: depend $(EXEC)
#
#exec: $(EXEC)
#	./$(EXEC)
#
#$(EXEC): $(OBJS)
#	$(CAMLC) $(CUSTOM) -o $(EXEC) $(LIBS) $(OBJS)
#
#.SUFFIXES:
#.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly
#
#.ml.cmo:
#	$(CAMLC) -c $<
#
#.mli.cmi:
#	$(CAMLC) -c $<
#
#clean:
#	rm -f *.cmo *.cmi *.json $(EXEC)
#
#depend: $(SOURCES)
#	$(CAMLDEP) *.mli *.ml > .depend
#
#include .depend