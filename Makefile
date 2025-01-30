# $TAG: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.27 $

include version
include config

world:
	cd tools; $(MAKE) all
	cp src/phox.native.hide src/phox.ml
	cd src; $(MAKE) all
	cd lib; $(MAKE) all

js:
	cp src/phox.js.hide src/phox.ml
	dune build --release ./src/phox.bc.js

local-js:
	cp src/phox.native.hide src/phox.ml
	dune build --release ./src/phox.bc.js
	for d in lib examples tutorial/* dnr/chapitre-*; do \
	  mkdir -p phox-js/$$d; \
	  rsync -avx $$d/Makefile $$d/*.phx  phox-js/$$d/; \
	  cd phox-js/$$d;\
          make depend ;\
          make PHOX='$(PHOXJS)' all;\
          cd -; \
	done

install-all: install installPG

install:
	if [ ! -f $(BINDIR) ] ; then sudo mkdir -p $(BINDIR) ; fi
	if [ ! -f $(LIBDIR) ] ; then sudo mkdir -p $(LIBDIR) ; fi
	if [ ! -f $(DOCDIR)/tools ] ; then sudo mkdir -p $(DOCDIR)/tools ; fi
	if [ ! -f $(TEXDIR) ] ; then sudo mkdir -p $(TEXDIR) ; fi
	if [ ! -f $(EXAMPLESDIR) ] ; then sudo mkdir -p $(EXAMPLESDIR) ; fi
	cd tools; sudo $(MAKE) -S install
	cd src; $(MAKE) -S install
	cd lib; sudo $(MAKE) -S install
	cd emacs; sudo $(MAKE) -S install
	cd tex; sudo $(MAKE) -S install
	cd doc; sudo $(MAKE) -S install
	if [ -f lib/TAGS ]; then sudo cp lib/TAGS $(LIBDIR); fi
	if [ -f doc/TAGS ]; then sudo cp doc/TAGS $(TEXTDOCDIR); fi
	sudo cp -r examples/* $(EXAMPLESDIR)
	sudo cp -r tutorial $(EXAMPLESDIR)
	if [ ! -z `which texhash` ]; then texhash; fi

WWW=/home/raffalli/WWW2/Raffalli/phox

phox-js/files.js: lib/*.phx examples/*.phx tutorial/*/*.phx
	- mkdir phox-js
	echo 'phoxMenus = [];' > phox-js/files.js; \
	for f in dnr/chapitre-* tutorial/* examples lib; do \
	  echo -n 'phoxMenus.push({ folder: "'$${f}'" , files: ["' >> phox-js/files.js; \
	  cd $$f; ls *.phx > tmp.txt; \
          cd -; cat $$f/tmp.txt | xargs echo -n | sed 's/ /", "/g' >> phox-js/files.js; \
	  rm $$f/tmp.txt; \
	  echo '"]});' >>  phox-js/files.js; \
        done

install-www: js phox-js/files.js
	rsync -r phox-js/* phox-js/files.js $(WWW)/online/
	rsync -r www/*.html www/pics www/*.js www/fonts $(WWW)/online/
	rsync _build/default/src/phox.bc.js $(WWW)/online/
	rsync doc/doc.pdf doc/libdoc.pdf $(WWW)/


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
	cd dnr/chapitre-1; $(MAKE) check
	cd dnr/chapitre-3; $(MAKE) check
	cd dnr/chapitre-4; $(MAKE) check

depend:
	cd examples; $(MAKE) depend
	cd tutorial/french; $(MAKE) depend
	cd tutorial/english; $(MAKE) depend
	cd dnr/chapitre-1; $(MAKE) depend
	cd dnr/chapitre-3; $(MAKE) depend
	cd dnr/chapitre-4; $(MAKE) depend

clean:
	./tools/cleandir .
	cd src; $(MAKE) clean
	cd lib; $(MAKE) clean
	cd doc; $(MAKE) clean
	cd tex; $(MAKE) clean
	cd doc; $(MAKE) clean
	cd examples; $(MAKE) clean
	if [ -d private ]; then  cd private; $(MAKE) clean; fi
	cd tutorial/french; $(MAKE) clean
	cd tutorial/english; $(MAKE) clean
	cd dnr/chapitre-1; $(MAKE) clean
	cd dnr/chapitre-3; $(MAKE) clean
	cd dnr/chapitre-4; $(MAKE) clean
	rm -rf phox-js
	cd tools; $(MAKE) clean

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
	cd dnr/chapitre-1; $(MAKE) veryclean
	cd dnr/chapitre-3; $(MAKE) veryclean
	cd dnr/chapitre-4; $(MAKE) veryclean
	rm -rf phox-js
	cd tools; $(MAKE) veryclean


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
