#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = exo-10_cor.phx exo-12_cor.phx exo-13_cor.phx exo-2_cor.phx \
        exo-6_cor.phx PA.phx

#exo-5_cor.phx exo-5.wt_cor.phx

all: $(SRCS:_cor.phx=_quest.phx)

check: $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	gawk -f ../../tools/phox_tut.awk $< > $@

.phx.phi:
	$(PHOX) -c $<

depend: $(SRCS)
	$(PHOXDEP) $(SRCS) > depend

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

include depend
