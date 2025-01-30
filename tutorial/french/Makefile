#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = tautologie_cor.phx commutation_cor.phx ideal_cor.phx sort_cor.phx \
       topo_cor.phx analyse_cor.phx group_cor.phx minlog_cor.phx \
       intro_cor.phx intro2_cor.phx heine_cor.phx noether_cor.phx \
       suite_cor.phx images_cor.phx

all: $(SRCS:_cor.phx=_quest.phx)

check: requis.phi $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	$(PHOXTUT) $< > $@

.phx.phi:
	$(PHOX) -c $<

depend: $(SRCS)
	$(PHOXDEP) $(SRCS) > depend

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

include depend
