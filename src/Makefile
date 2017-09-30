# $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.18 $

# You should not need to modify anything in this file. If you need to
# do so, report a bug so that I can modify my installation procedure.

CONFIGFILE=config
VERSFILE=version

# you should know what you are doing if you modify anything beyond this line

TARGET = phoxslow$(EXE)
TARGETO = phoxopt$(EXE)

include ../$(CONFIGFILE)
include ../$(VERSFILE)

############


$(TARGET) : version.ml
	ocamlbuild -pp camlp4o -pkgs num,unix main.byte
	ln -f _build/main.byte $@

$(TARGETO) : version.ml
	ocamlbuild -pp camlp4o -pkgs num,unix main.native
	ln -f _build/main.native $@

clean:
	ocamlbuild -clean
	- rm -rf *~ \#*\# $(TARGET) $(TARGETO)

veryclean: clean
	- rm -f version.ml .depend

.SUFFIXES :
.SUFFIXES : .mli .ml .cmi .cmx .cmo .o

version.ml: ../version ../config Makefile
	if [ -f version.ml ]; then rm -f version.ml; fi;\
	echo 'let version = "$(VERSNUM) "^$(VERSDAT)' > version.ml;\
	echo 'let default_path = "$(DEFAULT_PATH)"' >> version.ml;\
	echo "let delim = '$(DELIM)'" >> version.ml;\

install: $(PHOXVERS)
	cp $(PHOXVERS) $(BINDIR)/phox$(EXE)
