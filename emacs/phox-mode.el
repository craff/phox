;; phox.el

(require 'proof-site)
(proof-ready-for-assistant 'phox)

(require 'proof)
(require 'proof-easy-config)		; easy configure mechanism

(defconst phox-goal-regexp
  "\\(prop\\(osition\\)?\\)\\|\\(lem\\(ma\\)?\\)\\|\\(fact\\)\\|\\(cor\\(ollary\\)?\\)\\(theo\\(rem\\)?\\)")

(proof-easy-config
 'phox "phox"
 proof-prog-name		"phox"
 proof-terminal-string          "."
 proof-script-command-end-regexp"[.][ \n\t\r]"
 proof-script-comment-start	"(*"
 proof-script-comment-end	"*)"
 proof-script-syntax-table-entries
   '(?\( "()1"
     ?\) ")(4"
     ?* ". 23"
     ?$ "w"
     ?_ "w"
     ?. "w")
 proof-shell-syntax-table-entries
   '(?\( "()1"
     ?\) ")(4"
     ?* ". 23"
     ?$ "w"
     ?_ "w"
     ?. "w")
 proof-goal-command-regexp	(concat "^" phox-goal-regexp)
 proof-save-command-regexp	"^save"
 proof-goal-with-hole-regexp	(concat "^" phox-goal-regexp "\\(\\([a-zA-Z0-9_$]*\\)\\) ")
 proof-save-with-hole-regexp	"save \\(\\([a-zA-Z0-9_$]*\\)\\).[ \n\t\r]"
 proof-non-undoables-regexp	"\\(undo\\)\\|\\(abort\\)\\|\\(show\\)\\(.*\\)[ \n\t\r]"
 proof-goal-command		"fact \"%s\"."
 proof-save-command		"save \"%s\"."
 proof-kill-goal-command	"abort."
 proof-showproof-command	"goals."
 proof-undo-n-times-cmd		"undo %s."
 proof-auto-multiple-files	 t
 proof-shell-cd-cmd		 "cd \"%s\"."
 proof-shell-interrupt-regexp	 "Interrupt."
 proof-shell-start-goals-regexp	 "goal [0-9]+/[0-9]+"
 proof-shell-end-goals-regexp	 "%PhoX%"
 proof-shell-quit-cmd		 "quit."
 proof-assistant-home-page	 "http://www.lama.univ-savoie.fr/~raffalli/phox.html"
 proof-shell-annotated-prompt-regexp "^\\(>PhoX>\\)\\|\\(%PhoX%\\) "
 proof-shell-error-regexp	 "^.*[Ee]rror:.*"
 proof-shell-init-cmd		 ""
; proof-shell-proof-completed-regexp "^No subgoals!"
 proof-script-font-lock-keywords
   '("Cst" "Import" "Use" "Sort"
     "new_intro" "new_elim" "new_rewrite"
     "add_path" "author" "cd"
     "claim" "close_def" "def" "del" "documents"
     "depend" "elim_after_intro" "export"
     "edel" "eshow" "flag" "goal" "include"
     "institute" "path" "print_sort" "priority"
     "quit" "save" "search" "tex" "tex_syntax" "title"
     "proposition" "prop" "lemma" "lem" "fact" "corollary" "cor"
     "theorem" "theo"
                                        ; proof command, FIXME: another color
     "abort" "absurd" "apply" "axiom" "constraints"
     "elim" "from" "goals" "intros" "intro" "instance"
     "local" "lefts" "left" "next" "rewrite" "rewrite_hyp"
     "rename" "rmh" "trivial" "slh" "use" "undo" "unfold"
     "unfold_hyp")
   )


(defun phox-symbol-regex (str)
  "Gets a string, e.g. Alpha, returns the regexp matching the escaped
version of it in Phox code, with no chars in [a-z0-9A-Z] after it."
  (interactive "MString:")
  (concat "[^!%&*+,-/:;≤=>@\\^`#|~]\\(" str "\\)[^!%&*+,-/:;≤=>@\\^`#|~]"))

(defun phox-word-regex (str)
  "Gets a string, e.g. Alpha, returns the regexp matching the escaped
version of it in Phox code, with no chars in [a-z0-9A-Z] after it."
  (interactive "MString:")
  (concat "\\b\\(" str "\\)\\b"))

(add-to-list 'auto-mode-alist '("\\.phx\\'" . phox-mode))

(add-hook 'phox-mode-hook
	  (lambda () (set-input-method "TeX"))
	  5)

(provide 'phox-mode)
