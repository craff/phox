# $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.18 $

# You should not need to modify anything in this file. If you need to
# do so, report a bug so that I can modify my installation procedure.

#path
CONFIGFILE=config
VERSFILE=version
FILESEP=/
SHELL=sh


ZFLAGS = $(CAMLPREPRO) -rectypes

# you should know what you are doing if you modify anything beyond this line

TARGET = phoxslow$(EXE)
TARGETO = phoxopt$(EXE)

include ../$(CONFIGFILE)
include ../$(VERSFILE)

FILES = version.cmo restart.cmo lang.cmo basic.cmo myhashtbl.cmo undo.cmo \
	flags.cmo data_base.cmo cache.cmo data.cmo types.cmo  \
        local.cmo files.cmo option.cmo lexer.cmo typunif.cmo lambda_util.cmo \
        print.cmo typing.cmo parser.cmo safe_add.cmo data_info.cmo \
        af2_basic.cmo hilbert.cmo pattern.cmo module.cmo \
	bindlib.cmo lambda.cmo parse_lambda.cmo \
        type_check.cmo compile.cmo interact.cmo rewrite.cmo \
        inductive.cmo poids.cmo tex.cmo logic.cmo \
	typespoids.cmo splitting.cmo ptypes.cmo oldeduction.cmo affichage.cmo majlistes.cmo \
	prover.cmo af2_logic.cmo new_cmd.cmo  proof_general.cmo parse_cmd.cmo main.cmo

FILESO = $(FILES:.cmo=.cmx)

FILESML = $(FILES:.cmo=.ml)

FILESMLI = $(wildcard *.mli)

############


$(TARGET) : $(FILES)
	$(CAMLC) $(ZFLAGS) -o $@ unix.cma nums.cma $(FILES)

$(TARGETO) : $(FILESO)
	$(CAMLO) $(ZFLAGS) -o $@ unix.cmxa nums.cmxa $(FILESO)

clean:
	- rm -f *.cmo *.cmx *.cmi *.o $(TARGET) $(TARGETO)

veryclean: clean
	- rm -f version.ml .depend

.SUFFIXES :
.SUFFIXES : .mli .ml .cmi .cmx .cmo .o

.mli.cmi:
	$(CAMLC) $(ZFLAGS) -c $<

.ml.cmo:
	$(CAMLC) $(ZFLAGS) -c $<

.ml.cmx:
	$(CAMLO) $(ZFLAGS) -c $<

version.ml: ../version ../config Makefile
	if [ -f version.ml ]; then rm -f version.ml; fi;\
	echo 'let version = "$(VERSNUM) "^$(VERSDAT)' > version.ml;\
	echo 'let default_path = "$(DEFAULT_PATH)"' >> version.ml;\
	echo "let delim = '$(DELIM)'" >> version.ml;\

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),veryclean)
ifneq ($(MAKECMDGOALS),distclean)
.depend:  $(FILESML) $(FILESMLI)
	$(CAMLDEP) $(CAMLPREPRO) $(FILESML) $(FILESMLI) > .depend
endif
endif
endif

install: $(PHOXVERS)
	cp $(PHOXVERS) $(BINDIR)/phox$(EXE)

#dependencies
include .depend
