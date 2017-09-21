# $State: Exp $ $Date: 2000/10/12 09:58:25 $ $Revision: 1.1.1.1 $

include ../config

FILES = af2-mode.el sym-lock.el 

# Command for byte-compiling the files
COMPILECMD=(progn \
              (setq load-path (cons "." load-path)) \
              (byte-compile-file "af2-mode.el") \
              (if (string-match "XEmacs\\|Lucid" emacs-version) \
		(byte-compile-file "sym-lock.el")))

all: af2-mode.el 

af2-mode.el: af2-mode.tpl
	- rm -f af2-mode.el; \
	sed -e 's|%%LIBDIR%%|${LIBDIR}|' \
            -e 's|%%BINDIR%%|${BINDIR}|' \
            -e 's|%%DOCDIR%%|${DOCDIR}|' \
            af2-mode.tpl > af2-mode.el

clean:
	- rm -f af2-mode.el

veryclean: clean

install:
	@if test "$(EMACSDIR)" = ""; then \
          set xxx `($(EMACS) --batch --eval "(mapcar 'print load-path)") \
                   2>/dev/null | \
                   sed -n -e '/\/site-lisp/s/"//gp'`; \
          if test "$$2" = ""; then \
            set xxx `($(EMACS) --batch --eval "(mapcar 'print load-path)") \
                     2>/dev/null | \
                     sed -n -e '/\/site-packages/s/"//gp'`; \
	  fi; \
          if test "$$2" = ""; then \
            echo "Cannot determine Emacs site-lisp directory"; \
            echo "Set EMACSDIR in config"; \
            exit 2; \
          fi; \
          $(MAKE) EMACSDIR="$$2" simple-install; \
        else \
          $(MAKE) simple-install; \
        fi

simple-install: $(FILES)
	@echo "Installing in $(EMACSDIR)..."
	if test -d $(EMACSDIR); then : ; else mkdir -p $(EMACSDIR); fi
	cp $(FILES) $(EMACSDIR)
	cd $(EMACSDIR); $(EMACS) --batch --eval '$(COMPILECMD)'



 