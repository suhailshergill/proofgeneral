;; proof-syntax.el Generic font lock expressions
;; Copyright (C) 1997-1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequiera
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;


(require 'font-lock)
(require 'proof-config)

;; FIXME da: would regexp-opt be better here?  Or maybe
;;  (concat "\\<" (regexp-opt l) "\\>")
(defun proof-ids-to-regexp (l)
  "Maps a non-empty list of tokens `l' to a regexp matching any element"
  (mapconcat (lambda (s) (concat "\\<" s "\\>")) l "\\|"))

(defun proof-anchor-regexp (e)
  "Anchor (^) and group the regexp."
  (concat "^\\(" e "\\)"))

(defun proof-regexp-alt (&rest args)
  "Return the regexp which matches any of the regexps ARGS."
  ;; Is this not available in some library?
  (let ((res ""))
    (dolist (regexp args)
      (setq res (concat res (if (string-equal res "") "\\(" "\\|\\(")
			regexp "\\)")))
    res))

(defun proof-regexp-region (start end)
  "Return regexp matching START anything over several lines END."
  ;; FIXME: would like to use shy grouping here \\(?: but it seems
  ;; buggy or unimplemented in XEmacs.
  ;; WARNING: this produces nasty regexps that lead to stack
  ;; overflows.  It's better to have a loop that searches over lines,
  ;; see next function.
  (concat "\\(" start "\\)\\(\n\\|.\\)*\\(" end "\\)"))

(defun proof-re-search-forward-region (startre endre)
  "Search for a region delimited by regexps STARTRE and ENDRE.
Return the start position of the match for STARTRE, or
nil if a region cannot be found."
  (if (re-search-forward startre nil t)
      (let ((start (match-beginning 0)))
	(if (re-search-forward endre nil t)
	    start))))

;; Function for string matching that takes into account value
;; of proof-case-fold-search.  Last arg to string-match is
;; not applicable.

(defun proof-string-match (regexp string &optional start)
  "Like string-match, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (string-match regexp string start)))

(defun proof-string-match-safe (regexp string &optional start)
  "Like proof-string-match, but return nil if REGEXP is nil."
  (if regexp (proof-string-match regexp string start)))

(defun proof-stringfn-match (regexp-or-fn string)
  "Like proof-string-match if first arg is regexp, otherwise call it."
  (cond ((stringp regexp-or-fn)
	 (proof-string-match regexp-or-fn string))
	((functionp regexp-or-fn)
	 (funcall regexp-or-fn string))))

(defun proof-looking-at (regexp)
  "Like looking-at, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (looking-at regexp)))


;; Generic font-lock

(defvar proof-indent-commands-regexp ""
  "Subset of keywords and tacticals which are terminated by the
`proof-terminal-char'.  Basic indentation is provided automatically
for these.")


(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-unfontify-separator}.

(defun proof-ids (proof-id &optional sepregexp)
  "Generate a regular expression for separated lists of identifiers.
Default is comma separated, or SEPREGEXP if set."
  (concat proof-id "\\(\\s-*"   (or sepregexp ",") "\\s-*"
	  proof-id "\\)*"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A big hack to unfontify commas in declarations and definitions.  ;;
;; Useful for provers which have declarations of the form x,y,z:Ty  ;;
;; All that can be said for it is that the previous way of doing    ;;
;; this was even more bogus.                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Refontify the whole line, 'cos that's what font-lock-after-change
;; does.

;;FIXME: Under FSF Emacs 20.2, when initially fontifying the buffer,
;;       commas are not zapped. 
;; 
;; FIXME da: this should be more specific!!
;;
(defun proof-zap-commas-region (start end &optional length)
  "Remove the face of all `,' within the region (START,END).
The optional argument LENGTH has no effect. It is required so that we
may assign this function to `after-change-function'."
  (save-excursion
    (let 
	((start (progn (goto-char start) (beginning-of-line) (point)))
	 (end (progn (goto-char end) (end-of-line) (point))))
      (goto-char start)
      (while (search-forward "," end t)
	(if (memq (get-char-property (- (point) 1) 'face)
		(list 'proof-declaration-name-face
		  'font-lock-function-name-face))
	    (font-lock-unfontify-region (- (point) 1) (point))
	    )))))

(defun proof-zap-commas-buffer () 
  "Remove the face of all `,' in the current buffer."
  (proof-zap-commas-region (point-min) (point-max)))

(defun proof-unfontify-separator ()
     (make-local-variable 'after-change-functions)
     (setq after-change-functions
	   (append (delq 'proof-zap-commas-region after-change-functions)
		   '(proof-zap-commas-region))))

;;
;; Functions for doing something like "format" but with customizable
;; control characters.
;;
;; Added for version 3.1 to help quote funny characters in filenames.
;;

(defun proof-format (alist string)
  "Format a string by matching regexps in ALIST against STRING"
  (while alist
    (let ((idx 0))
      (while (string-match (car (car alist)) string idx)
	(setq string
	      (concat (substring string 0 (match-beginning 0))
		      (cdr (car alist))
		      (substring string (match-end 0))))
	(setq idx (+ (match-beginning 0) (length (cdr (car alist)))))))
    (setq alist (cdr alist)))
  string)

(defun proof-format-filename (string filename)
  "Format STRING by replacing %e, %r by escaped version of FILENAME.

%e uses the canonicalized expanded version of filename (including
directory, using default-directory -- see `expand-file-name').

%r uses the unadjusted (possibly relative) version of FILENAME.

%s means the same as %e.

Using %e can avoid problems with dumb proof assistants who don't
understand ~, for example."  
  (proof-format 
   (list (cons "%s" (proof-format proof-shell-filename-escapes 
				  (expand-file-name filename)))
	 (cons "%e" (proof-format proof-shell-filename-escapes 
				  (expand-file-name filename)))
	 (cons "%r" (proof-format proof-shell-filename-escapes 
				  (expand-file-name filename))))
   string))
 

(provide 'proof-syntax)
