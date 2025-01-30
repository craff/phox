#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = tautology_cor.phx sort_cor.phx topo_cor.phx commutation_cor.phx
all: $(SRCS:_cor.phx=_quest.phx)

check: $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	gawk -f ../../tools/phox_tut.awk $< > $@

.phx.phi:
	$(PHOX) -c $<

.PHONY: .depend
depend: $(SRCS)
	$(PHOXDEP) *.phx > depend

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

#include depend
