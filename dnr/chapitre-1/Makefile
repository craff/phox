#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES:
.SUFFIXES: _cor.phx _quest.phx _cor.phi .phx .phi

SRCS = exo-11_cor.phx exo-15_cor.phx exo-17_cor.phx exo-19_cor.phx \
       exo-21_cor.phx exo-8_cor.phx exo-13_cor.phx exo-16_cor.phx \
       exo-18_cor.phx exo-20_cor.phx exo-7_cor.phx

all: $(SRCS:_cor.phx=_quest.phx)

check: $(SRCS:_cor.phx=_cor.phi)

_cor.phx_quest.phx:
	$(PHOXTUT) $< > $@

.phx.phi:
	$(PHOX) -c $<

.PHONY: depend
depend: $(SRCS)
	echo ${ROOT_DIR}
	$(PHOXDEP) $(SRCS) > depend

clean:
	- rm *.phi *.pho

veryclean: clean
	- rm -f depend *_quest.phx

include depend
