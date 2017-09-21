#path
include ../config


.SUFFIXES:
.SUFFIXES:.phx .pho .phi .dvi .tex

.phx.phi:
	../src/$(PHOXVERS) -I ../lib -c $<

.tex.dvi:
	latex $<

default: all

check: all

depend: *.phx
	if [ -x ../tools/phoxdep ]; then ../tools/phoxdep -i../src/$(PHOXVERS) -I../lib *.phx > depend; fi

clean:
	- rm -f *.pho *.phi *.tex *.aux *.log *.dvi *.pin *.pout

veryclean: clean
	- rm -f depend

include depend
