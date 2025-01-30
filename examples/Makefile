#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES:
.SUFFIXES:.phx .pho .phi .dvi .tex

.phx.phi:
	$(PHOX) -I ../lib -c $<

.tex.dvi:
	latex $<

default: all

check: all

.PHONY: depend
depend: *.phx
	$(PHOXDEP) *.phx > depend

clean:
	- rm -f *.pho *.phi *.tex *.aux *.log *.dvi *.pin *.pout

veryclean: clean
	- rm -f depend

include depend
