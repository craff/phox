# $State: Exp $ $Date: 2004/01/08 17:23:28 $ $Revision: 1.3 $

include ../config

all: $(PRETTYVERS)

mall: all

prettyslow$(EXE): pretty.ml
	$(CAMLC) $(CAMLPREPRO) -o prettyslow pretty.ml

prettyopt$(EXE): pretty.ml
	$(CAMLO) $(CAMLPREPRO) -o prettyopt pretty.ml

clean:
	rm -f *.o *.cmx *.cmi *.cmo prettyslow prettyopt *.pout *.pin

veryclean: clean

install:
	cp $(PRETTYVERS) $(BINDIR)/pretty$(EXE); \
	cp *.tex *.sty $(TEXDIR)
