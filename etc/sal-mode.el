;;
;; SAL 3.1, Copyright (C) 2006, 2011, SRI International.  All Rights Reserved.
;;
;; SAL is free software; you can redistribute it and/or 
;; modify it under the terms of the GNU General Public License 
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of 
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
;; GNU General Public License for more details. 
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software 
;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA. 
;;

(require 'derived)
(require 'cl)

;; define several category of keywords
(setq sal-keywords '("context" "type" "begin" "end" "datatype" "module" 
                     "array" "of" "with" "to" "lambda" "forall" "exists"
                     "let" "in" "if" "then" "else" "elsif" "endif"
                     "input" "output" "global" "local" "definition" 
                     "initialization" "transition" "rename" "module" "theorem"
                     "lemma" "claim" "\\importing" "prefix" "suffix" "ringset"
                     "scalarset" "implements" "observe" "context" 
                     "TYPE" "BEGIN" "END" "DATATYPE" "MODULE" "CONTEXT" 
                     "WITH" "TO" "LAMBDA" "FORALL" "EXISTS" "LET" "IN" "IF"
                     "THEN" "ELSE" "ELSIF" "ENDIF" "INPUT" "OUTPUT" "GLOBAL" 
                     "LOCAL" "DEFINITION" "INITIALIZATION" "TRANSITION" "RENAME"
                     "MODULE" "THEOREM" "LEMMA" "CLAIM" "\\IMPORTING" "PREFIX"
                     "SUFFIX" "RINGSET" "SCALARSET" "IMPLEMENTS" "OBSERVE"))

(setq sal-types '("integer" "natural" "nzinteger" "real" "nzreal" "boolean" "int"
                  "nat" "bool" "INTEGER" "NATURAL" "NZINTEGER" "REAL" "NZREAL"
                  "BOOLEAN" "ARRAY" "OF"))

(setq sal-builtin '("and" "not" "or" "xor" "false" "true" "mod" "div" 
                    "AND" "NOT" "OR" "XOR" "FALSE" "TRUE" "MOD" "DIV" 
                    "ring_succ" "ring_pred"))

;; generate regex string for each category of keywords
(setq sal-keywords-regexp (regexp-opt sal-keywords 'words))
(setq sal-types-regexp (regexp-opt sal-types 'words))
(setq sal-builtin-regexp (regexp-opt sal-builtin 'words))

(defvar sal-font-lock-keywords
  `(
    ("%[^\n]*" . 'font-lock-comment-face)
    (,sal-keywords-regexp . 'font-lock-keyword-face)
    (,sal-builtin-regexp . 'font-lock-builtin-face)
    (,sal-types-regexp . 'font-lock-type-face)
    "Default font-lock-keywords for sal mode."
    )
  )

(defvar sal-mode-map ()
  "Local keymap used for SAL mode.")

(defvar sal-mode-hook nil
  "*List of functions to call when SAL mode is invoked.
This is a good place to add SAL environment specific bindings.")

(defvar sal-mode-syntax-table nil
  "Syntax table for SAL.")

;; Indentation rules :
;; These rules apply WHEN we see the line (no need to know the context to apply them)
;; Another understanding : these rules apply DIRECTLY to the line we see
;; Example :
;; BEGIN
;;   some code
;;   END (-> we need to indent this line, we don't need to know where it comes from
;;           we just need to find the corresponding BEGIN)
;; 
;; RULE 1 : If we see "END" we align it with the "BEGIN" or "DATAYPE" corresponding to it
;; RULE 2 : If we see a keyword except BEGIN we align it with the last keyword 
;;          or indent it corresponding to the last BEGIN
;; RULE 3 : If we see [] or [ alone we align it with the last []
;;          or TRANSITION keyword
;; RULE 4 : If we see BEGIN we align it with the last keyword 
;; RULE 5 : If we see }; we need to align it with the corresponding line containing {
;; 
;; RULE 6 : If we see ; we need to align it with the corresponding line containing ;
;; 
;; These rules apply AFTER we've seen the line and its context
;; The regexps correspond to the lines above, not the line we want to indent
;; (Examples :
;; TRANSITION (we look above looking for the last BEGIN indentation and we 
;;             increment it)
;; myvar = 2; (we look above looking for :
;;               - a keyword : indentation incremented
;;               - anything else : aligned with it)
;; 
;; BACKWARD CONTEXTING : No rule applies on the current line, we need to read the previous ones
;;   CONTEXT RULE 1 : If we see ";" it means we're at the end of a declaration
;;                    we set the identation to the value before the declaration depending
;;                    whether we're in a function or above a keyword
;;   CONTEXT RULE 2 : If we see a keyword (we are not one, or RULE 2 would have been applied)
;;                    We increment the indentation
;;   CONTEXT RULE 3 : If we see a "id : type =" then we're in the body of a declaration, we
;;                    increment the indentation
;;                    If we see a transition declaration then it's body should be indented
;;                    The body of a transition corresponds to the code between "-->" and "[]"
;;   CONTEXT RULE 4 : If the line we see ends with : or | w're in a declaration and we should 
;;                    increment the line
;;   NO CONTEXT :     We found no interesting context, no indentation

(defcustom sal-default-indent 2
  "*Default indentation.

Global indentation variable (large values may lead to indentation overflows).
When no governing keyword is found, this value is used to indent the line
if it has to."
  :type 'integer)

(setq sal-lvl1-keywords '("context" "end" "module" "input" "output" "global" "local"
                          "definition" "initialization" "transition" "module" "theorem"
                          "lemma" "implements" "context" 
                          "CONTEXT" "END" "MODULE" "INPUT" "OUTPUT" "GLOBAL" "LOCAL"
                          "DEFINITION" "INITIALIZATION" "TRANSITION" "MODULE" "THEOREM"
                          "LEMMA" "IMPLEMENTS" "CONTEXT" 
                          ))


(setq init-regexp "\\(.*: \\|[ \\\t]*\\)")
(setq sal-indent-lvl1-regexp (concat (concat init-regexp (regexp-opt sal-lvl1-keywords)) ";?"))

(setq function-trans-regexp "\\(\\(.*(.*)*\\|[ \\t]*\\)=\\|.*-->\\|.*\\[\\]\\)$")
(setq semicolon-regexp ".*;$")
(setq end-regexp (concat init-regexp "END\\(;?\\)"))
(setq begin-regexp (concat init-regexp "BEGIN"))
(setq sqbrack-regexp "^[ \t]*\\(\\(\\[\\]?\\)\\|\\]\\)")
(setq sqbrack-trans-regexp "^[ \t]*\\(\\[\\]?\\|TRANSITION\\)")
(setq colon-bang-regexp "^[^\n%]*\\(:\\||\\)$")
(setq end-array-decl "^[^\n{]*\\\};$")

(defun sal-indent-line ()
  "Indent current line as SAL code"
  (beginning-of-line)
  (if (bobp)
      ;; Beginning of buffer, first line is always non-indented
      (indent-line-to 0)
    ;; Not beginning of buffer
    (let ((not-indented t) cur-indent)

      ;; Defining a function to change the indentation based on the current one
      (defun change-indent (v) 
        (setq cur-indent (+ (current-indentation) v))
        (setq not-indented nil)
        )

      ;; Don't move the cursor while searching backward
      (save-excursion
        ;; RULE 1 : If we see "END" we align it with the "BEGIN" or "DATAYPE" corresponding to it
        (if (looking-at end-regexp) 
            ;; RULE 1 APPLIES
            (let ((nb-end 1))
              (message "Rule 1")
              (while (> nb-end 0)
                (forward-line -1)
                (if (looking-at begin-regexp)
                    (progn
                      (message "Rule 1 : Begin")
                      (setq nb-end (1- nb-end))
                      )
                  (if (looking-at "^[ \t]*.DATATYPE")
                      (progn
                        (message "Rule 1 : Data Type")
                        (setq nb-end 0)
                        )
                    ;; If we see END it means we have to go over the next BEGIN
                    (when (looking-at end-regexp)
                      (message "Rule 1 : End")
                      (setq nb-end (1+ nb-end))
                      ))))
              (setq cur-indent (current-indentation)))
          ;; RULE 1 DOESN'T APPLY, CHECK RULE 2
          ;; RULE 2 : If we see a keyword except BEGIN we align it with the last keyword
          ;;          or indent it corresponding to the last BEGIN
          (if (looking-at sal-indent-lvl1-regexp)
              ;; RULE 2 APPLIES
              (progn
                (message "Rule 2")
                (while not-indented
                  (forward-line -1)
                  (if (looking-at sal-indent-lvl1-regexp)
                      (change-indent 0)
                    (if (looking-at begin-regexp)
                        (change-indent sal-default-indent)
                      (when (bobp) (setq not-indented nil))
                      )
                    )
                  )
                )
            ;; RULE 2 DOESN'T APPLY, CHECK RULE 3
            ;; RULE 3 : If we see [] or [ alone we align it with the last []
            ;;          or TRANSITION keyword
            (if (looking-at sqbrack-regexp)
                ;; RULE 3 APPLIES
                (progn
                  (message "Rule 3")
                  (while not-indented
                    (forward-line -1)
                    (if (looking-at sqbrack-trans-regexp)
                        (change-indent 0)
                      (when (bobp) 
                        (message "Rule 3 BOBP")
                        (setq not-indented nil))
                      )
                    )
                  )
              ;; RULE 3 DOESN'T APPLY, CHECK RULE 4
              ;; RULE 4 : If we see BEGIN we align it with the last keyword 
              (if (looking-at begin-regexp)
                  ;; RULE 4 APPLIES
                  (progn
                    (message "Rule 4")
                    (while not-indented
                      (forward-line -1)
                      (if (looking-at sal-indent-lvl1-regexp)
                          (change-indent 0)
                        (when (bobp) (setq not-indented nil))
                        )
                      )
                    )
                ;; RULE 5 : If we see }; we need to align it with the corresponding line containing {
                (if (looking-at end-array-decl) 
                    ;; RULE 5 APPLIES
                    (let ((nb-brack 1))
                      (message "Rule 5")
                      (while (> nb-brack 0)
                        (forward-line -1)
                        (if (looking-at ".*{.*")
                            (progn
                              (message "Rule 5 {")
                              (setq nb-brack (1- nb-brack))
                              )
                          (if (looking-at end-array-decl)
                              (progn
                                (message "Rule 5 }")
                                (setq nb-brack (1+ nb-brack))
                                )
                            (when (bobp)
                              (message "Rule 5 bobp")
                              (setq nb-brack 0)
                              )
                            )
                          )
                        )
                      (setq cur-indent (current-indentation)))
                  ;; RULE 6 : If we see ; we need to align it with the corresponding line containing ;
                  (if (looking-at semicolon-regexp)
                      (progn
                        (message "Rule 6")
                        ;; RULE 6 APPLIES
                        ;; We need to find the last function/transition declaration or last ; or keyword
                        (while not-indented
                          (forward-line -1)
                          (if (or (looking-at function-trans-regexp) (looking-at sal-indent-lvl1-regexp))
                              (progn 
                                (message "Rule 6 : Function")
                                (change-indent sal-default-indent)
                                )
                            (if (looking-at semicolon-regexp)
                                (progn 
                                  (message "Rule 6 : ;")
                                  (change-indent 0)
                                  )
                              (when (bobp) 
                                (setq not-indented nil))
                              )
                            )
                          )
                        )
                    ;; RULE 6 DOESN'T APPLY : BACKWARD CONTEXTING
                    (while not-indented
                      ;; Go back to one line above
                      (forward-line -1)
                      ;; CONTEXT RULE 1 : If we see ";" it means we're at the end of a function/transition declaration
                      ;;                  we set the identation to the value before the declaration
                      (if (looking-at semicolon-regexp)
                          (progn
                            (message "Context Rule 1")
                            ;; CONTEXT RULE 1 APPLIES
                            ;; We need to find the last function/transition declaration
                            (while not-indented
                              (forward-line -1)
                              (if (or (looking-at function-trans-regexp) (looking-at sal-indent-lvl1-regexp))
                                  (progn 
                                    (message "Context Rule 1 : Function / Keyword")
                                    (change-indent sal-default-indent)
                                    )
                                (when (bobp) (setq not-indented nil))
                                )
                              )
                            )
                        ;; CONTEXT RULE 1 DOESN'T APPLY, CHECK CONTEXT RULE 2
                        ;; CONTEXT RULE 2 : If we see a keyword (we are not one, or RULE 2 would have been applied)
                        ;;                  We increment the indentation
                        (if (looking-at sal-indent-lvl1-regexp)
                            ;; CONTEXT RULE 2 APPLIES
                            (progn
                              (message "Context Rule 2")
                              (change-indent sal-default-indent)
                              )
                          ;;   CONTEXT RULE 3 : If we see a "id : type =" then we're in the body of a declaration, we
                          ;;                    increment the indentation
                          ;;                    If we see a transition declaration then it's body should be indented
                          ;;                    The body of a transition corresponds to the code between "-->" and "[]"

                          (if (looking-at function-trans-regexp)
                              (progn
                                (message "Context Rule 3")
                                (change-indent sal-default-indent)
                                )
                            ;;   CONTEXT RULE 4 : If the line we see ends with : or | we're in a declaration and we should 
                            ;;                    increment the line
                            (if (looking-at colon-bang-regexp)
                                (progn
                                  (message "Context Rule 4")
                                  (change-indent sal-default-indent)
                                  )
                              ;; NO CONTEXT : We found no interesting context, no indentation
                              (message "No Context")
                              
                              (when (bobp) (setq not-indented nil))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      ;; Indentation relatively to what was calculated
      ;; (when (< cur-indent 0)
      ;;   (setq cur-indent 0))
      
      (if cur-indent
          (indent-line-to cur-indent)
        ;; If we didn't see an indentation hint, then allow no indentation
        (indent-line-to 0)))))

(defun sal-create-syntax-table ()
  "Create the syntax table for SAL mode."
  (setq sal-mode-syntax-table (make-syntax-table))
  
  ;; A % starts a comment
  (modify-syntax-entry ?% "<" sal-mode-syntax-table)
  ;; A \f and \n end a comment
  (modify-syntax-entry ?\n ">" sal-mode-syntax-table)

  (modify-syntax-entry ?:  "." sal-mode-syntax-table)
  (modify-syntax-entry ?\; "." sal-mode-syntax-table)
  (modify-syntax-entry ?\|  "." sal-mode-syntax-table)
  (modify-syntax-entry ?+  "." sal-mode-syntax-table)
  (modify-syntax-entry ?-  "." sal-mode-syntax-table)
  (modify-syntax-entry ?*  "." sal-mode-syntax-table)
  (modify-syntax-entry ?/  "." sal-mode-syntax-table)
  (modify-syntax-entry ?=  "." sal-mode-syntax-table)
  (modify-syntax-entry ?<  "." sal-mode-syntax-table)
  (modify-syntax-entry ?>  "." sal-mode-syntax-table)
  (modify-syntax-entry ?. "." sal-mode-syntax-table)
  (modify-syntax-entry ?\\ "." sal-mode-syntax-table)
  (modify-syntax-entry ?\' "." sal-mode-syntax-table)
  (modify-syntax-entry ?# "." sal-mode-syntax-table)

  ;; define parentheses to match
  (modify-syntax-entry ?\( "()" sal-mode-syntax-table)
  (modify-syntax-entry ?\) ")(" sal-mode-syntax-table)
  (modify-syntax-entry ?\[ "(]" sal-mode-syntax-table)
  (modify-syntax-entry ?\] ")[" sal-mode-syntax-table)
  (modify-syntax-entry ?\{ "(}" sal-mode-syntax-table)
  (modify-syntax-entry ?\} "){" sal-mode-syntax-table)
  (set-syntax-table sal-mode-syntax-table))

;;;###autoload
(defun sal-mode ()
  "SAL mode is a major mode for editing SAL code."
  (interactive)
  (kill-all-local-variables)

  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)

  (make-local-variable 'comment-start)
  (setq comment-start "%")

  ;; comment end must be set because it may hold a wrong value if
  ;; this buffer had been in another mode before. RE
  (make-local-variable 'comment-end)
  (setq comment-end "")

  (make-local-variable 'comment-start-skip) ;; used by autofill
  (setq comment-start-skip "%+[ \t]*")

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'sal-indent-line)
  
  (make-local-variable 'fill-column)
  (setq fill-column 75)
  
  (make-local-variable 'comment-column)
  (setq comment-column 40)

  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments t)

  (make-local-variable 'case-fold-search)
  (setq case-fold-search t)

  (setq major-mode 'sal-mode)
  (setq mode-name "SAL")

  (use-local-map sal-mode-map)

  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(sal-font-lock-keywords nil nil ((?_ . "w"))))

  (if sal-mode-syntax-table
      (set-syntax-table sal-mode-syntax-table)
    (sal-create-syntax-table))

  (run-hooks 'sal-mode-hook))

;; clear memory. no longer needed
(setq sal-keywords nil)
(setq sal-types nil)
(setq sal-builtin nil)

;; clear memory. no longer needed
(setq sal-keywords-regexp nil)
(setq sal-types-regexp nil)
(setq sal-builtin-regexp nil)


(provide 'sal-mode)
