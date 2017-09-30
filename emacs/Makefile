# $State: Exp $ $Date: 2000/10/12 09:58:25 $ $Revision: 1.1.1.1 $

include ../config

FILES = phox.el

all:

clean:

veryclean: clean

install:
	if [ -d $(PGDIR) ]; then\
	  if [ ! -d $(PGPHOXDIR) ]; then\
		mkdir $(PGPHOXDIR);\
	  fi;\
	  cp -f *.el $(PGPHOXDIR);\
	fi
