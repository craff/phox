#path
include ../../config


.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = tautology_cor.phx sort_cor.phx topo_cor.phx commutation_cor.phx 
all: $(SRCS:_cor.phx=_quest.phx)

check: $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	gawk -f ../../tools/phox_tut.awk $< > $@

.phx.phi:
	../../src/$(PHOXVERS) -I ../../lib -c $<

depend: $(SRCS)
	if [ -x ../../tools/phoxdep ]; then ../../tools/phoxdep -i ../../src/$(PHOXVERS) -I ../../lib *.phx > depend; fi

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

#include depend
