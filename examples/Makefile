#path
include ../config

PHOXPATH=../_build/default/src/phox.exe

.SUFFIXES:
.SUFFIXES:.phx .pho .phi .dvi .tex

.phx.phi:
	$(PHOXPATH) -I ../lib -c $<

.tex.dvi:
	latex $<

default: all

check: all

depend: *.phx
	../tools/phoxdep -I../lib *.phx > depend

clean:
	- rm -f *.pho *.phi *.tex *.aux *.log *.dvi *.pin *.pout

veryclean: clean
	- rm -f depend

include depend
