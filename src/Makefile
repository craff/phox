# You should not need to modify anything in this file. If you need to
# do so, report a bug so that I can modify my installation procedure.

CONFIGFILE=config
VERSFILE=version

# you should know what you are doing if you modify anything beyond this line

TARGET = phox

include ../$(CONFIGFILE)
include ../$(VERSFILE)

version.ml: ../version ../config Makefile
	if [ -f version.ml ]; then rm -f version.ml; fi;\
	echo 'let version = "$(VERSNUM) "^$(VERSDAT)' > version.ml;\
	echo 'let default_path = "$(DEFAULT_PATH)"' >> version.ml;\
	echo "let delim = '$(DELIM)'" >> version.ml;\

############

all: version.ml
	cd ..; dune build --release

clean:
	cd ..; dune clean

veryclean: clean
	- rm -f version.ml phox.ml

.SUFFIXES :
.SUFFIXES : .mli .ml .cmi .cmx .cmo .o

install:
	dune install
	sudo cp $$(which phox) $(BINDIR)
