#all: garbage_bin.pdf citizen.pdf mincitizen.pdf simplecitizen.pdf basiccitizen.pdf truck.pdf simplecitizen_bin.pdf basiccitizen_bin.pdf
#all: garbage_bin.pdf basiccitizen.pdf basiccitizen_bin.pdf
all: garbage_bin.pdf basictruck.pdf basictruck_bin.pdf

basiccitizen_bin.pdf: basiccitizen_bin.dot
	dot -Tpdf basiccitizen_bin.dot -o basiccitizen_bin.pdf

basictruck_bin.pdf: basictruck_bin.dot
	dot -Tpdf basictruck_bin.dot -o basictruck_bin.pdf

garbage_bin.pdf: garbage_bin.dot
	dot -Tpdf garbage_bin.dot -o garbage_bin.pdf

basictruck.pdf: basictruck.dot
	dot -Tpdf basictruck.dot -o basictruck.pdf

basiccitizen.pdf: basiccitizen.dot
	dot -Tpdf basiccitizen.dot -o basiccitizen.pdf

simplecitizen.pdf: simplecitizen.dot
	dot -Tpdf simplecitizen.dot -o simplecitizen.pdf

mincitizen.pdf: mincitizen.dot
	dot -Tpdf mincitizen.dot -o mincitizen.pdf

citizen.pdf: citizen.dot
	dot -Tpdf citizen.dot -o citizen.pdf

truck.pdf: truck.dot
	dot -Tpdf truck.dot -o truck.pdf

garbage_bin.dot truck.dot citizen.dot: componi
	./componi

componi: componi.ml
	ocamlc -g -o componi componi.ml

.PHONY: all
