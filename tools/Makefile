# $State: Exp $ $Date: 2002/01/17 16:13:19 $ $Revision: 1.4 $

include ../config

all: chmodcleandir phoxdep phoxx.awk phox_tex.awk \
	 phox_tut.awk phox_tags.awk phox_etags.sh

mall: all paraserver pararun

chmodcleandir:
	chmod a+x cleandir

update: update.ml
	cslc unix.cmxa update.ml -cclib -lunix -o update

pararun: pararun.ml
	cslc unix.cmxa pararun.ml -cclib -lunix -o pararun

paraserver: paraserver.ml
	cslc unix.cmxa paraserver.ml -cclib -lunix -o paraserver

phoxdep: phoxdep.tpl
	- rm -f phoxdep; \
	echo "#!"${PERL} > phoxdep; \
	chmod a+x phoxdep; \
        cat phoxdep.tpl >> phoxdep

phoxx.awk: phoxx.tpl
	- rm -f phoxx.awk; \
	echo "#!"${AWK} -f > phoxx.awk; \
	chmod a+x phoxx.awk; \
        cat phoxx.tpl >> phoxx.awk

phox_tex.awk: phox_tex.tpl
	- rm -f phox_tex.awk; \
	echo "#!"${AWK} -f > phox_tex.awk; \
	chmod a+x phox_tex.awk; \
        cat phox_tex.tpl >> phox_tex.awk

phox_tut.awk: phox_tut.tpl
	- rm -f phox_tut.awk; \
	echo "#!"${AWK} -f > phox_tut.awk; \
	chmod a+x phox_tut.awk; \
        cat phox_tut.tpl >> phox_tut.awk

phox_tags.awk: phox_tags.tpl
	- rm -f phox_tags.awk; \
	echo "#!"${AWK} -f > phox_tags.awk; \
	chmod a+x phox_tags.awk; \
        cat phox_tags.tpl >> phox_tags.awk

phox_etags.sh: phox_etags.tpl
	- rm -f phox_etags.sh; \
	sed -e 's|%%DOCDIR%%|${DOCDIR}|' \
            phox_etags.tpl > phox_etags.sh; \
	chmod a+x phox_etags.sh

clean:
	- rm -f *.cmo *.cmi *.cmx *.o update pararun paraserver phoxdep \
          phoxx.awk phox_tex.awk phox_tut.awk  phox_tags.awk phox_etags.sh

veryclean: clean
	- rm -f camldep camloodep update pararun paraserver


install:
	cp phoxdep $(BINDIR); \
	if test -d $(DOCDIR)/tools; then : ; else mkdir $(DOCDIR)/tools; fi; \
	cp phox_etags.sh phox_tags.awk  phoxx.awk $(DOCDIR)/tools


 