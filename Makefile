#all: garbage_bin.pdf citizen.pdf mincitizen.pdf simplecitizen.pdf basiccitizen.pdf truck.pdf simplecitizen_bin.pdf basiccitizen_bin.pdf
#all: garbage_bin.pdf basiccitizen.pdf basiccitizen_bin.pdf
all: garbage_bin.pdf basictruck.pdf citizen.pdf bascitruck_bin.pdf

citizen_bin.pdf: citizen_bin.dot
	dot -Tpdf citizen_bin.dot -o citizen_bin.pdf

mincitizen_bin.pdf: mincitizen_bin.dot
	dot -Tpdf mincitizen_bin.dot -o mincitizen_bin.pdf

basictruck_bin.pdf: basictruck_bin.dot
	dot -Tpdf basictruck_bin.dot -o basictruck_bin.pdf

garbage_bin.pdf: garbage_bin.dot
	dot -Tpdf garbage_bin.dot -o garbage_bin.pdf

basictruck.pdf: basictruck.dot
	dot -Tpdf basictruck.dot -o basictruck.pdf

basiccitizen.pdf: basiccitizen.dot
	dot -Tpdf basiccitizen.dot -o basiccitizen.pdf

mincitizen.pdf: mincitizen.dot
	dot -Tpdf mincitizen.dot -o mincitizen.pdf

simplecitizen.pdf: simplecitizen.dot
	dot -Tpdf simplecitizen.dot -o simplecitizen.pdf

citizen.pdf: citizen.dot
	dot -Tpdf citizen.dot -o citizen.pdf

truck.pdf: truck.dot
	dot -Tpdf truck.dot -o truck.pdf

garbage_bin.dot basictruck.dot bascitruck_bin.dot citizen.dot: componi
	./componi

componi: componi.ml
	ocamlc -g -o componi componi.ml

.PHONY: all
