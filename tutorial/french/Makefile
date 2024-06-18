#path
include ../../config

PHOXPATH=../../_build/default/src/phox.exe

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = tautologie_cor.phx commutation_cor.phx ideal_cor.phx sort_cor.phx \
       topo_cor.phx analyse_cor.phx group_cor.phx minlog_cor.phx \
       intro_cor.phx intro2_cor.phx heine_cor.phx noether_cor.phx \
       suite_cor.phx images_cor.phx

all: $(SRCS:_cor.phx=_quest.phx)

check: requis.phi $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	gawk -f ../../tools/phox_tut.awk $< > $@

.phx.phi:
	$(PHOXPATH) -I ../../lib -c $<

depend: $(SRCS)
	../../tools/phoxdep -I ../../lib $(SRCS) > depend

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

include depend
