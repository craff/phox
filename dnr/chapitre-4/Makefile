#path
include ../../config

PHOXPATH=../../_build/default/src/phox.exe

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = exo-1_cor.phx exo-7_cor.phx

all: $(SRCS:_cor.phx=_quest.phx)

check: $(SRCS:_cor.phx=_cor.phi)

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
