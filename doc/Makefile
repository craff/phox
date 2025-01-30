# $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.8 $

MAKETEXT= $(AWK) -f ../tools/phoxx.awk
MAKETEX = $(AWK) -f ../tools/phox_tex.awk

include ../config

.SUFFIXES :
.SUFFIXES : .phx .pht .tex .pdf

SRCS = $(shell cd ../lib ; ls *.phx)

VPATH = ../lib

all: text doc.pdf libdoc.pdf

.phx.pht:
	- rm -f $@; \
	$(MAKETEXT) $< > $@

.phx.tex:
	- rm -f $@; \
	$(MAKETEX) ../lib/$< > tmp.phx; \
	export PHOXPATH=../lib; \
	$(PHOX) -c tmp.phx; \
	rm -f tmp.phx ; \
	mv tmp.doc.tex $@

.tex.pdf:
	- export TEXINPUTS=../tex:; \
	touch $(<:.tex=).ind; \
	xelatex -shell-escape $<; \
	$(PRETTY) $(<:.tex=); \
	bibtex $(<:.tex=); \
	makeindex $(<:.tex=).idx; \
	xelatex -shell-escape $<; \
	$(PRETTY) $(<:.tex=); \
	makeindex $(<:.tex=).idx; \
	xelatex -shell-escape $<

text: $(SRCS:.phx=.pht)

tex: $(SRCS:.phx=.tex)

#tex: $(SRCS:.phx=.tex)
#	mv -f $(SRCS:.phx=.tex)  TEX/

examples.phi: examples.phx
	export PHOXPATH=../lib; \
	$(PHOX) -c examples.phx

basic.phi: basic.phx
	export PHOXPATH=../lib; \
	$(PHOX) -c basic.phx

doc.pdf: *.tex *.bib examples.phi basic.phi

libdoc.pdf: tex

clean:
	- ../tools/cleandir .; \
	rm -f *.aux *.toc *.bbl *.blg *.log *.idx *.pin *.pout \
	   *.ilg *.ind *.pho *.phi doc/TMP_* doc/images.* doc/*.pl \
           *.*.tex TEX/* $(SRCS) $(SRCS:.phx=.tex) *.dview *.wiz .\#* \
           *.fmt *.dvi *.pht *.out ecran.fig.bak ; \
	rm -rf doc libdoc; \
	rm -rf .advi* _whizzy_* ._whizzy_*
	cd english/intro; rm -f *.aux *.toc *.bbl *.blg *.log *.idx *.pin *.pout \
	   *.ilg *.ind *.pho *.phi doc/TMP_* doc/images.* doc/*.pl \
           *.*.tex TEX/* $(SRCS) $(SRCS:.phx=.tex) *.dview *.wiz .\#* \
           *.fmt *.dvi *.pht *.out ecran.fig.bak
	cd french/intro; rm -f *.aux *.toc *.bbl *.blg *.log *.idx *.pin *.pout \
	   *.ilg *.ind *.pho *.phi doc/TMP_* doc/images.* doc/*.pl \
           *.*.tex TEX/* $(SRCS) $(SRCS:.phx=.tex) *.dview *.wiz .\#* \
           *.fmt *.dvi *.pht *.out ecran.fig.bak

veryclean: clean
	- rm -f doc.pdf libdoc.pdf $(SRCS:.phx=.pht); rm -rf doc
	- rm english/intro/phox_intro.pdf
	- rm french/intro/phox_intro.pdf

install: # doc.pdf libdoc.pdf $(SRCS:.phx=.pht)
	if test -d $(TEXTDOCDIR); then : ; else mkdir $(TEXTDOCDIR); fi; \
	if test -d $(HTMLDOCDIR); then : ; else mkdir $(HTMLDOCDIR); fi; \
	cp *.pht $(TEXTDOCDIR); \
	cp doc.pdf libdoc.pdf $(DOCDIR); \
	if test -f doc/doc.html; then cp -r doc/* $(HTMLDOCDIR) ; fi
