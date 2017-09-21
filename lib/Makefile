# $State: Exp $ $Date: 2001/01/18 10:18:46 $ $Revision: 1.4 $

#path
include ../config

.SUFFIXES :
.SUFFIXES : .phx .pho .phi

SRCS =  prop.phx set.phx bin_rel.phx bool.phx nat_def.phx nat_ax.phx nat.phx \
	product.phx sum.phx list.phx list_nat_ax.phx list_nat.phx \
	quotient.phx rel_def.phx ac.phx

all: depend $(SRCS:.phx=.phi)

.phx.phi: 
	../src/$(PHOXVERS) -I . -c $<

prop.phi: prop.phx ../src/$(PHOXVERS)
	../src/$(PHOXVERS) -I . -c -init prop.phx

depend: Makefile $(SRCS)
	if [ -x ../tools/phoxdep ]; then ../tools/phoxdep -i../src/$(PHOXVERS) $(SRCS) > depend; fi

install: $(LIBS)
	cp *.phi *.pho *.phx $(LIBDIR)

clean:
	- rm -f *.phi *.pho *.tex *.aux *.log *.dvi *.pin *.pout 

veryclean: clean
	- rm -f depend TAGS

#dependencies
include depend
