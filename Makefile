# $TAG: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.27 $

include version
include config

world:
	cd tools; $(MAKE) all
	cd src; $(MAKE) $(PHOXVERS)
	cd tex; $(MAKE) $(PRETTYVERS)
	cd lib; $(MAKE) all

install-all: install installPG

install:
	if [ ! -f $(BINDIR) ] ; then mkdir -p $(BINDIR) ; fi
	if [ ! -f $(LIBDIR) ] ; then mkdir -p $(LIBDIR) ; fi
	if [ ! -f $(DOCDIR)/tools ] ; then mkdir -p $(DOCDIR)/tools ; fi
	if [ ! -f $(TEXDIR) ] ; then mkdir -p $(TEXDIR) ; fi
	if [ ! -f $(EXAMPLESDIR) ] ; then mkdir -p $(EXAMPLESDIR) ; fi
	cd tools; $(MAKE) -S install
	cd src; $(MAKE) -S install
	cd lib; $(MAKE) -S install
	cd emacs; $(MAKE) -S install
	cd tex; $(MAKE) -S install
	cd doc; $(MAKE) -S install
	if [ -f lib/TAGS ]; then cp lib/TAGS $(LIBDIR); fi
	if [ -f doc/TAGS ]; then cp doc/TAGS $(TEXTDOCDIR); fi
	cp -r examples/* $(EXAMPLESDIR)
	cp -r tutorial $(EXAMPLESDIR)
	if [ ! -z `which texhash` ]; then texhash; fi

uninstall:
	- rm -rf $(LIBDIR) $(DOCDIR) $(TEXDIR)
	- rm $(BINDIR)/phox$(EXE)
	- rm $(BINDIR)/phoxdep
	- rm $(BINDIR)/pretty$(EXE)

tags:
	cd lib; ../tools/phox_etags.sh *.phx
	cd doc; ../tools/phox_etags.sh *.pht

docs:
	cd doc; $(MAKE)

check:
	cd examples; $(MAKE) check
	cd tutorial/french; $(MAKE) check
	cd tutorial/english; $(MAKE) check

depend:
	cd examples; $(MAKE) depend
	cd tutorial/french; $(MAKE) depend
	cd tutorial/english; $(MAKE) depend

clean:
	./tools/cleandir .
	cd tools; $(MAKE) clean
	cd src; $(MAKE) clean
	cd lib; $(MAKE) clean
	cd doc; $(MAKE) clean
	cd tex; $(MAKE) clean
	cd doc; $(MAKE) clean
	cd examples; $(MAKE) clean
	if [ -d private ]; then  cd private; $(MAKE) clean; fi
	cd tutorial/french; $(MAKE) clean
	cd tutorial/english; $(MAKE) clean

veryclean:
	./tools/cleandir .
	cd tools; $(MAKE) veryclean
	cd src; $(MAKE) veryclean
	cd lib; $(MAKE) veryclean
	cd doc; $(MAKE) veryclean
	cd tex; $(MAKE) veryclean
	cd examples; $(MAKE) veryclean
	if [ -d private ]; then cd private; $(MAKE) veryclean; fi
	cd tutorial/french; $(MAKE) veryclean
	cd tutorial/english; $(MAKE) veryclean
	rm -f doc/TAGS lib/TAGS

distclean: veryclean

distrib1:
	$(MAKE)
	$(MAKE) docs
	$(MAKE) tags

distrib2:
	if test -f config.dev ; then echo Warning: config.dev exists; exit 1; fi
	$(MAKE) clean
	find . -name .\#\* -print -exec rm \{\} \;
	if test -d $(DISTRIBDIR); then : ; else mkdir -p $(DISTRIBDIR); fi
	cp doc/doc.pdf $(DISTRIBDIR)/phox.doc.pdf
	gzip $(DISTRIBDIR)/phox.doc.pdf
	cp doc/libdoc.pdf $(DISTRIBDIR)/phox.libdoc.pdf
	gzip $(DISTRIBDIR)/phox.libdoc.pdf
	if test -L /tmp/$(DISTRIBTARDIR) ; then rm -f /tmp/$(DISTRIBTARDIR); fi
	ln -s `pwd` /tmp/$(DISTRIBTARDIR)
	tar --dereference --directory=/tmp --exclude=archive --exclude .git  \
	    -cvf $(DISTRIBDIR)/phox.tar $(DISTRIBTARDIR)
	rm -f /tmp/$(DISTRIBTARDIR)
	gzip $(DISTRIBDIR)/phox.tar
#	tar --exclude RCS -cvf phox.doc.html.tar doc; \
#       gzip phox.doc.html.tar; \


distrib:
	$(MAKE) distrib1
	$(MAKE) distrib2

release: distclean
	git push origin
	git tag -a $(VERSNUM) -m "phox on github"
	git push origin $(VERSNUM)
