# $State: Exp $ $Date: 2004/01/08 17:23:28 $ $Revision: 1.3 $

include ../config

all: $(PRETTYVERS)

mall: all

prettyslow$(EXE): pretty.ml
	ocamlbuild -pp camlp4o pretty.byte
	ln -f _build/pretty.byte $@

prettyopt$(EXE): pretty.ml
	ocamlbuild -pp camlp4o pretty.native
	ln -f _build/pretty.native $@

clean:
	ocamlbuild -clean
	rm -f prettyslow$(EXE) prettyopt$(EXE) *.pout *.pin *~ \#*\#

veryclean: clean

install:
	cp $(PRETTYVERS) $(BINDIR)/pretty$(EXE); \
	cp *.tex *.sty $(TEXDIR)
