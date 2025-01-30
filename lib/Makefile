#path
include $(shell git rev-parse --show-toplevel)/config

.SUFFIXES :
.SUFFIXES : .phx .pho .phi

SRCS =  prop.phx set.phx bin_rel.phx bool.phx nat_def.phx nat_ax.phx nat.phx \
	product.phx sum.phx list.phx list_nat_ax.phx list_nat.phx \
	quotient.phx rel_def.phx ac.phx

all: depend $(SRCS:.phx=.phi)

.phx.phi:
	$(PHOX) -c $<

prop.phi: prop.phx
	$(PHOX)  -c -init prop.phx

.PHONY: depend
depend: Makefile $(SRCS)
	$(PHOXDEP) $(SRCS) > depend

install: $(LIBS)
	cp *.phi *.pho *.phx $(LIBDIR)

clean:
	- rm -f *.phi *.pho *.tex *.aux *.log *.dvi *.pin *.pout

veryclean: clean
	- rm -f depend TAGS

#dependencies
include depend
