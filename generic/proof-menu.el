;; proof-menu.el  Menus, keymaps, and misc commands for Proof General
;;
;; Copyright (C) 2000,2001 LFCS Edinburgh. 
;; Authors:   David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(require 'proof-toolbar)     ; needed for proof-toolbar-scripting-menu

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Miscellaneous commands
;;;

(defvar proof-display-some-buffers-count 0)

(defun proof-display-some-buffers ()
  "Display the reponse, goals, trace, or shell buffer, rotating.
A fixed number of repetitions of this command switches back to
the same buffer.
Also move point to the end of the response buffer if it's selected.
If in three window or multiple frame mode, display two buffers."
  (interactive)
  ;; The GUI-tessence here is to implement a humane toggle, which
  ;; allows habituation.  E.g. two taps of C-c C-l always
  ;; shows the goals buffer, three the trace buffer, etc.
  ;; (That behaviour makes less sense from the menu, though,
  ;;  where it seems more natural just to rotate from last 
  ;;  position)
  (cond 
   ((and (interactive-p) 
	 (eq last-command 'proof-display-some-buffers))
    (incf proof-display-some-buffers-count))
   (t
    (setq proof-display-some-buffers-count 0)))
  (let* ((assocbufs   (remove-if-not 'buffer-live-p 
				    (list proof-response-buffer
					  proof-goals-buffer
					  proof-thms-buffer
					  proof-trace-buffer)))
					;proof-shell-buffer
	 (selectedbuf (nth (mod proof-display-some-buffers-count 
				(length assocbufs)) assocbufs)))
    (cond
     ((or proof-three-window-mode proof-multiple-frames-enable)
      ;; Display two buffers: next in rotation and goals/response
      ;; FIXME: this doesn't work as well as it might.
      (proof-switch-to-buffer selectedbuf 'noselect)
      (proof-switch-to-buffer (if (eq selectedbuf proof-goals-buffer)
				  proof-response-buffer
				proof-goals-buffer) 'noselect))
     (selectedbuf
      (proof-switch-to-buffer selectedbuf 'noselect)))
    (if (eq selectedbuf proof-response-buffer)
	(set-window-point (get-buffer-window proof-response-buffer)
			  (point-max)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Key bindings
;;;

;;;###autoload
(defun proof-menu-define-keys (map)
;; M-a and M-e are usually {forward,backward}-sentence.
;; Some modes also override these with similar commands
(define-key map [(meta a)] 'proof-backward-command)
(define-key map [(meta e)] 'proof-forward-command)
(define-key map [(meta up)] 'proof-backward-command)
(define-key map [(meta down)] 'proof-forward-command)
(define-key map [(control meta a)] 'proof-goto-command-start)
(define-key map [(control meta e)] 'proof-goto-command-end)
(define-key map [(control c) (control a)] (proof-ass keymap))
(define-key map [(control c) (control b)] 'proof-process-buffer)
;; C-c C-c is proof-interrupt-process in universal-keys
(define-key map [(control c) (control f)] 'proof-find-theorems)
(define-key map [(control c) (control h)] 'proof-help)
(define-key map [(control c) (control l)] 'proof-display-some-buffers)
(define-key map [(control c) (control n)] 'proof-assert-next-command-interactive)
(define-key map [(control c) (control p)] 'proof-prf)
(define-key map [(control c) (control r)] 'proof-retract-buffer)
(define-key map [(control c) (control s)] 'proof-toggle-active-scripting)
(define-key map [(control c) (control t)] 'proof-ctxt)
(define-key map [(control c) (control u)] 'proof-undo-last-successful-command)
;; C-c C-w is pg-response-clear-displays in universal-keys
(define-key map [(control c) (control z)] 'proof-frob-locked-end)
(define-key map [(control c) (control backspace)] 'proof-undo-and-delete-last-successful-command)
; C-c C-v is proof-minibuffer-cmd in universal-keys
(define-key map [(control c) (control ?.)] 'proof-goto-end-of-locked)
(define-key map [(control c) (control return)] 'proof-goto-point)
(define-key map [(control c) v] 'pg-toggle-visibility);; FIXME: FSF??
(cond ((string-match "XEmacs" emacs-version)
(define-key map [(control button3)]	  'proof-mouse-goto-point)
(define-key map [(control button1)]	  'proof-mouse-track-insert)) ; no FSF
      (t 
(define-key map [(control mouse-3)]	  'proof-mouse-goto-point)))
 ; FSF
;; NB: next binding overwrites comint-find-source-code.  
;; FIXME: not implemented yet 
;; (define-key map [(meta p)]		  'proof-previous-matching-command)
;; (define-key map [(meta n)]		  'proof-next-matching-command)
;; Standard binding for completion
(define-key map [(control return)] 'proof-script-complete)
(define-key map [(control c) (control ?\;)] 'pg-insert-last-output-as-comment)
;;
;; Experimental: span moving functions
(if proof-experimental-features (progn
      (define-key map [(control meta up)] 'pg-move-region-up)
      (define-key map [(control meta down)] 'pg-move-region-down)))
;; Add the universal keys bound in all PG buffers.
;; C-c ` is next-error in universal-keys
(proof-define-keys map proof-universal-keys))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Functions to define the menus
;;;

;; The main Proof-General generic menu

;;;###autoload
(defun proof-menu-define-main ()
  (easy-menu-define 
   proof-mode-menu  
   proof-mode-map
   "The main Proof General menu"
   proof-main-menu))

;; The proof assistant specific menu

;;;###autoload
(defun proof-menu-define-specific ()
  (easy-menu-define 
   proof-assistant-menu 
    proof-mode-map
    (concat "The menu for " proof-assistant)
    (cons proof-assistant
	  (append
	   (proof-ass menu-entries)
	   '("----")
	   (or proof-menu-favourites
	       (proof-menu-define-favourites-menu))
	   (or proof-menu-settings
	       (proof-menu-define-settings-menu))
	   '("----")
	   (list
	    (vector
	     (concat "Start " proof-assistant)
	     'proof-shell-start
	     ':active '(not (proof-shell-live-buffer)))
	    (vector
	     (concat "Exit " proof-assistant)
	     'proof-shell-exit
	     ':active '(proof-shell-live-buffer)))
	   '("----")
	   (list
	    (cons "Help"
		  (append
		   `([,(concat proof-assistant " information")
		      '(proof-help)
		      ,menuvisiblep proof-info-command]
		     [,(concat proof-assistant " web page")
		      '(browse-url proof-assistant-home-page)
		      ,menuvisiblep proof-assistant-home-page])
		   (proof-ass help-menu-entries))))))))
	   

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Contents of the menus
;;;

(defvar proof-help-menu
  '("Help"
    ["PG Info"      	(info "ProofGeneral") t]
    ["PG Homepage"  	(browse-url proof-general-home-page) t]
    ["About PG"        proof-splash-display-screen t]
    ["Send Bug Report" proof-submit-bug-report t])
  "Proof General help menu.")

(defvar proof-show-hide-menu
  '(("Show all"
     ["Proofs"    (pg-show-all-portions "proof") t]
     ["Comments"  (pg-show-all-portions "comment") t])
    ("Hide all"
     ["Proofs"    (pg-show-all-portions "proof" 'hide) t]
     ["Comments"  (pg-show-all-portions "comment" 'hide) t]))
  "Show/hide submenu.")

(defvar proof-buffer-menu
  (cons "Buffers"
	'(["Active Scripting"
	    (proof-switch-to-buffer proof-script-buffer)
	    :active (buffer-live-p proof-script-buffer)]
	   ["Rotate Output Buffers"
	    proof-display-some-buffers
	    :active (buffer-live-p proof-goals-buffer)]
	   ;;["Goals"
	   ;; (proof-switch-to-buffer proof-goals-buffer t)
	   ;; :active (buffer-live-p proof-goals-buffer)]
	   ;;["Response"
	   ;; (proof-switch-to-buffer proof-response-buffer t)
	   ;; :active (buffer-live-p proof-response-buffer)]
	   ["Shell"
	    (proof-switch-to-buffer proof-shell-buffer)
	    :active (buffer-live-p proof-shell-buffer)]
	   ;; FIXME: this next test doesn't work since menus
	   ;; loaded before proof-shell-trace-output-regexp is
	   ;; set (in proof-shell hook).  Should be better with
	   ;; simplified customization mechanism.
	   ;; ( if proof-shell-trace-output-regexp ... )
	   ;;'(["Trace"
	   ;;(proof-switch-to-buffer proof-trace-buffer)
	   ;;:active (buffer-live-p proof-trace-buffer)])
	   ["Clear Responses"
	    pg-response-clear-displays
	    :active (buffer-live-p proof-response-buffer)]))
  "Proof General buffer menu.")


;; Make the togglers used in options menu below

(proof-deftoggle proof-three-window-mode)
(proof-deftoggle proof-script-fly-past-comments)
(proof-deftoggle proof-delete-empty-windows)
(proof-deftoggle proof-shrink-windows-tofit)
(proof-deftoggle proof-multiple-frames-enable proof-multiple-frames-toggle)
(proof-deftoggle proof-output-fontify-enable proof-output-fontify-toggle)
(proof-deftoggle proof-disappearing-proofs)
(proof-deftoggle-fn (proof-ass-sym x-symbol-enable) 'proof-x-symbol-toggle)

(defvar proof-quick-opts-menu
  (cons 
   "Options"
   `(["Electric Terminator" proof-electric-terminator-toggle
     :style toggle
     :selected proof-electric-terminator-enable]
     ["Fly Past Comments" proof-script-fly-past-comments-toggle
      ,menuvisiblep (not proof-script-use-old-parser)
      :style toggle
      :selected proof-script-fly-past-comments]
     ["Disppearing Proofs" proof-disappearing-proofs-toggle 
      :style toggle
      :selected proof-disappearing-proofs]
     ["Output Highlighting" proof-output-fontify-toggle
      :active t
      :style toggle
      :selected proof-output-fontify-enable]
     ["X-Symbol" proof-x-symbol-toggle
      :active (proof-x-symbol-support-maybe-available)
      :style toggle
      :selected (proof-ass x-symbol-enable)]
     ["Toolbar" proof-toolbar-toggle
      ;; should really be split into :active & GNU Emacs's :visible
      :active (and (or (featurep 'toolbar) (featurep 'tool-bar))
			 (boundp 'proof-buffer-type)
			 ;; only allow toggling of toolbar enable in one
			 ;; buffer to avoid strange effects because we
			 ;; only keep one flag.  (Strange effects because 
			 ;; we only turn it off in one buffer at a time)
			 (eq proof-buffer-type 'script))
      :style toggle
      :selected proof-toolbar-enable]
     ("Display"
      ["Three Window Mode" proof-three-window-mode-toggle
      :active (not proof-multiple-frames-enable)
      :style toggle
      :selected proof-three-window-mode]
     ["Delete Empty Windows" proof-delete-empty-windows-toggle
      :active (not proof-multiple-frames-enable)
      :style toggle
      :selected proof-delete-empty-windows]
     ["Shrink to Fit" proof-shrink-windows-tofit-toggle
      :active (not proof-multiple-frames-enable)
      :style toggle
      :selected proof-shrink-windows-tofit]
     ["Multiple Frames" proof-multiple-frames-toggle
      :active (display-graphic-p)
      :style toggle
      :selected proof-multiple-frames-enable])
     ("Follow Mode" 
      ["Follow Locked Region" 
       (customize-set-variable 'proof-follow-mode 'locked)
       :style radio
       :selected (eq proof-follow-mode 'locked)]
      ["Keep Locked Region Displayed" 
       (customize-set-variable 'proof-follow-mode 'follow)
       :style radio
       :selected (eq proof-follow-mode 'follow)]
      ["Never Move" 
       (customize-set-variable 'proof-follow-mode 'ignore)
       :style radio
       :selected (eq proof-follow-mode 'ignore)])
     "----"
     ["Save Options" (proof-quick-opts-save) t]))
  "Proof General quick options.")

(defun proof-quick-opts-save ()
  "Save current values of PG Options menu items using Custom."
  (interactive)
  (pg-custom-save-vars
   'proof-disappearing-proofs 
   'proof-multiple-frames-enable
   'proof-three-window-mode
   'proof-delete-empty-windows
   'proof-multiple-frames-enable
   'proof-output-fontify-enable
   'proof-toolbar-enable
   'proof-script-fly-past-comments
   (proof-ass-sym x-symbol-enable)
   'proof-follow-mode))

(defconst proof-config-menu
  (list "----"
	;; buffer menu might better belong in toolbar menu?
	proof-buffer-menu
	proof-quick-opts-menu)
  "Proof General configuration menu.")

(defconst proof-advanced-menu
  (cons "Advanced..."
	(append
	 `(["Function Menu" function-menu
	    ,menuvisiblep (fboundp 'function-menu)]
	   ["Complete Identifier" proof-script-complete t])
	 (list "-----")
	 proof-show-hide-menu
	 (list "-----")
	 ;; NB: customize-menu-create was buggy in earlier 
	 ;; Emacs 21.X; okay since 21.1.1
	 (list (customize-menu-create 'proof-general))
	 (list (customize-menu-create 'proof-general-internals 
				      "Internals"))))
  "Advanced sub-menu of script functions and customize.")


(defvar proof-menu  
  '(["Next Error" proof-next-error
     :active pg-next-error-regexp]
    ["Scripting Active" proof-toggle-active-scripting
     :style toggle
     :selected (eq proof-script-buffer (current-buffer))])
  "The Proof General generic menu for scripting buffers.")


(defvar proof-main-menu
  (cons proof-general-name
	(append
	 proof-toolbar-scripting-menu
	 proof-menu
	 proof-config-menu
	 (list proof-advanced-menu)
	 (list proof-help-menu)))
  "PG main menu used in scripting buffers.")

(defvar proof-aux-menu
  (cons proof-general-name 
	(append
	 proof-toolbar-scripting-menu
	 proof-config-menu
	 (list proof-help-menu)))
  "PG auxiliary menu used in non-scripting buffers.")




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Favourites mechanism for prover-specific menu
;;;

(defvar proof-menu-favourites nil
  "The Proof General favourites menu for the current proof assistant.")

(defun proof-menu-define-favourites-menu ()
  "Return menu generated from `PA-favourites'."
  (let ((favs (reverse (proof-ass favourites))) ents)
    (while favs
      (setq ents (cons (apply 'proof-def-favourite (car favs)) ents))
      (setq favs (cdr favs)))
    (setq proof-menu-favourites 
	  (list 
	   (cons "Favourites" 
		 (append ents
			 ;; (list "----")  doesn't work for adding before
			 '(["Add Favourite" 
			    (call-interactively 'proof-add-favourite) t]
			   ["Delete Favourite" 
			    (call-interactively 'proof-del-favourite) t]
			   ["Save Favourites"
			    (proof-save-favourites) t])))))))
  
;;; Define stuff from favourites

;;;###autoload
(defmacro proof-defshortcut (fn string &optional key)
  "Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof-assistant map."
  (if key
      (eval ;; eval-after-load "proof" ?
       `(define-key (proof-ass keymap) (quote ,key) (quote ,fn))))
  `(defun ,fn ()
     ,(concat "Shortcut command to insert " string " into the current buffer.")
     (interactive)
     (proof-insert ,string)))

(defmacro proof-definvisible (fn string &optional key)
  "Define function FN to send STRING to proof assistant, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is sent using proof-shell-invisible-command, which see.
KEY is added onto proof-assistant map."
  (if key
      (eval ;; eval-after-load "proof" ?
       `(define-key (proof-ass keymap) (quote ,key) (quote ,fn))))
  `(defun ,fn ()
     ,(concat "Command to send " string " to the proof assistant.")
     (interactive)
     (proof-shell-invisible-command ,string)))

(defun proof-def-favourite (command inscript menuname &optional key new)
  "Define and a \"favourite\" proof assisant function.
See doc of `proof-add-favourite' for first four arguments.
Extra NEW flag means that this should be a new favourite, so check
that function defined is not already bound.
This function defines a function and returns a menu entry 
suitable for adding to the proof assistant menu."
  (let* ((menunames	(split-string (downcase menuname)))
	 (menuname-sym  (proof-sym (proof-splice-separator "-" menunames)))
	 (menu-fn	menuname-sym) (i 1))
    (while (and new (fboundp menu-fn))
      (setq menu-fn (intern (concat (symbol-name menuname-sym)
				    "-" (int-to-string i))))
      (incf i))
    (if inscript
	(eval `(proof-defshortcut ,menu-fn ,command ,key))
      (eval `(proof-definvisible ,menu-fn ,command ,key)))
    ;; Return menu entry
    (vector menuname menu-fn t)))


;;; Code for adding "favourites" to the proof-assistant specific menu

(defvar proof-make-favourite-cmd-history nil
  "History for proof-make-favourite.")

(defvar proof-make-favourite-menu-history nil
  "History for proof-make-favourite.")

(defun proof-save-favourites ()
  "Save favourites in customization settings."
  (interactive)
  (pg-custom-save-vars (proof-ass-sym favourites)))

(defun proof-del-favourite (menuname)
  "Delete \"favourite\" command recorded at MENUNAME."
  (interactive
   (list
    (completing-read "Menu item to delete: " 
		     (mapcar 'cddr (proof-ass favourites))
		     nil t)))
  (let*
      ((favs       (proof-ass favourites))
       (rmfavs	   (remove-if 
		    (lambda (f) (string-equal menuname (caddr f)))
		    favs)))
    (unless (equal favs rmfavs)
      (easy-menu-remove-item proof-assistant-menu 
			     '("Favourites") menuname)
      (customize-set-variable  (proof-ass-sym favourites) rmfavs))))
  
(defun proof-read-favourite ()
  (let* 
      ((guess  (buffer-substring (save-excursion
				   (beginning-of-line-text)
				   (point)) (point)))
       (cmd (read-string
	     (concat "Command to send to " proof-assistant ": ") 
	     guess
	     proof-make-favourite-cmd-history))
       (ins (y-or-n-p "Should command be recorded in script? "))
       (men (read-string
	     "Name of command on menu: " 
	     cmd
	     proof-make-favourite-menu-history))
       (key (if (y-or-n-p "Set a keybinding for this command? : ")
		;; FIXME: better validation here would be to check
		;; this is a new binding, or remove old binding below.
		(events-to-keys
		 (read-key-sequence 
		  "Type the key to use (binding will be C-c C-a <key>): " 
		  nil t)))))
    ;; result
    (list cmd ins men key)))
	  

(defun proof-add-favourite (command inscript menuname &optional key)
  "Define and add a \"favourite\" proof-assisant function to the menu bar.
The favourite function will issue COMMAND to the proof assistant.  
COMMAND is inserted into script (not sent immediately) if INSCRIPT non-nil.
MENUNAME is the name of the function for the menu.
KEY is the optional key binding."
  (interactive (proof-read-favourite))
  (let*
      ((menu-entry (proof-def-favourite command inscript menuname key t))
       (favs       (proof-ass favourites))
       (rmfavs	   (remove-if 
		    (lambda (f) (string-equal menuname (caddr f)))
		    favs))
       (newfavs    (append 
		    rmfavs 
		    (list (list command inscript menuname key)))))
    ;; If def succeeds, add to customize var
    (customize-set-variable  (proof-ass-sym favourites) newfavs)
    (easy-menu-add-item proof-assistant-menu 
			'("Favourites") menu-entry "Add Favourite")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Proof assistant settings mechanism.
;;;

(defvar proof-assistant-settings nil
 "A list of default values kept in Proof General for current proof assistant.
A list of lists (SYMBOL SETTING TYPE) where SETTING is a string value
to send to the proof assistant using the value of SYMBOL and 
and the function `proof-assistant-format'.  The TYPE item determines
the form of the menu entry for the setting.")

(defvar proof-menu-settings nil
  "Settings submenu for Proof General.")

(defun proof-menu-define-settings-menu ()
  "Return menu generated from `proof-assistant-settings'."
  (let ((setgs proof-assistant-settings) ents)
    (while setgs
      (setq ents (cons 
		  (apply 'proof-menu-entry-for-setting (car setgs)) ents))
      (setq setgs (cdr setgs)))
    (if ents
	(setq proof-menu-settings 
	      (list (cons "Settings" ents))))))

(defun proof-menu-entry-name (symbol)
  "Return a nice menu entry name for SYMBOL."
  (upcase-initials 
   (replace-in-string (symbol-name symbol) "-" " ")))

(defun proof-menu-entry-for-setting (symbol setting type)
  (let ((entry-name  (proof-menu-entry-name symbol))
	(pasym	     (proof-ass-symv symbol)))
    (cond
     ((eq type 'boolean)
      (vector entry-name 
	      (proof-deftoggle-fn pasym)
	      :style 'toggle
	      :selected pasym))
     ((eq type 'integer)
      (vector entry-name 
	      (proof-defintset-fn pasym)
	      t))
     ((eq type 'string)
      (vector entry-name 
	      (proof-defstringset-fn pasym)
	      t)))))

;;; autoload for compiled version: used in macro proof-defpacustom
;;;###autoload
(defun proof-defpacustom-fn (name val args)
  "As for macro `defpacustom' but evaluation arguments."
  (let (newargs setting evalform type)
    (while args
      (cond 
       ((eq (car args) :setting)
	(setq setting (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :eval)
	(setq evalform (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :type)
	(setq type (cadr args))
	(setq newargs (cons (car args) newargs)))
       (t
	(setq newargs (cons (car args) newargs))))
      (setq args (cdr args)))
    (setq newargs (reverse newargs))
    (unless (or setting evalform)
      (error "defpacustom: missing :setting or :eval keyword"))
    (unless (and type
		  (or (eq (eval type) 'boolean) 
		      (eq (eval type) 'integer) 
		      (eq (eval type) 'string)))
      (error "defpacustom: missing :type keyword or wrong :type value"))
    (if (assoc name proof-assistant-settings)
	(error "defpacustom: Proof assistanting setting %s already defined!"
	       name))
    ;; Could consider moving the bulk of the remainder of this
    ;; function to a function proof-assistant-setup-settings which
    ;; defines the custom vals *and* menu entries.   This would
    ;; allow proof assistant customization to manipulate
    ;; proof-assistant-settings directly rather than forcing
    ;; use of defpacustom.  (Probably stay as we are: more abstract)
    (eval
     `(defpgcustom ,name ,val
	,@newargs
	:set 'proof-set-value
	:group 'proof-assistant-setting))
    (if evalform
	(eval
	 `(defpgfun ,name ()
	    ,evalform))
      (eval
       `(defpgfun ,name ()
	  (proof-assistant-invisible-command-ifposs
	   (proof-assistant-settings-cmd (quote ,name))))))
    (setq proof-assistant-settings
	  (cons (list name setting (eval type)) proof-assistant-settings))))

;;;###autoload
(defmacro defpacustom (name val &rest args)
  "Define a setting NAME for the current proof assitant, default VAL.
NAME can correspond to some internal setting, flag, etc, for the
proof assistant, in which case a :setting and :type value should be provided.
The :type of NAME should be one of 'integer, 'boolean, 'string.
The customization variable is automatically in group `proof-assistant-setting.
The function `proof-assistant-format' is used to format VAL.
If NAME corresponds instead to a PG internal setting, then a form :eval to
evaluate can be provided instead."
  `(proof-defpacustom-fn (quote ,name) (quote ,val) (quote ,args)))

(defun proof-assistant-invisible-command-ifposs (cmd)
  "Send CMD as an \"invisible command\" if the proof process is available."
  ;; FIXME: better would be to queue the command, or even interrupt a
  ;; queue in progress.  Also must send current settings at start of
  ;; session somehow.  (This might happen automatically if a queue of
  ;; deffered commands is set, since defcustom calls proof-set-value
  ;; even to set the default/initial value?)
  (if (proof-shell-available-p)
      (progn
	(proof-shell-invisible-command cmd t)
	;; refresh display, 
	;; FIXME: should only do if goals display is active,
	;; messy otherwise. 
	;; (we need a new flag for "active goals display").  
	(if proof-showproof-command 
	    (proof-shell-invisible-command proof-showproof-command))
	;;  Could also repeat last command if non-state destroying.
	)))


(defun proof-assistant-settings-cmd (&optional setting)
  "Return string for making setting vals kept in Proof General customizations.
If SETTING is non-nil, return a string for just that setting. 
Otherwise return a string for configuring all settings."
  (let
      ((evalifneeded (lambda (expr)
			(if (and (cadr expr) ;; setting has PA string?
				 (or (not setting) 
				     (eq setting (car expr))))
			    (proof-assistant-format 
			     (cadr expr) 
			     (eval (proof-ass-symv (car expr))))))))
    (apply 'concat (mapcar evalifneeded 
			   proof-assistant-settings))))

(defun proof-assistant-format (string curvalue)
  "Replace a format characters %b %i %s in STRING by formatted CURVALUE.
Formatting suitable for current proof assistant, controlled by
`proof-assistant-format-table' which see.
Finally, apply `proof-assistant-setting-format' if non-nil.
As a special case for boolean settings: the setting STRING 
can be a cons cell of two strings, the first one for true (non-nil
value) and the second for false."
  (let ((setting
	 (if (consp string)
	     (if curvalue (car string) (cdr string))
	   ;; Otherwise must use % format characters
	   (proof-format proof-assistant-format-table string))))
    (if proof-assistant-setting-format
	(funcall proof-assistant-setting-format setting)
      setting)))

(defvar proof-assistant-format-table 
  (list
   (cons "%b" '(proof-assistant-format-bool curvalue))
   (cons "%i" '(proof-assistant-format-int curvalue))
   (cons "%s" '(proof-assistant-format-string curvalue)))
  "Table to use with `proof-format' for formatting CURVALUE for assistant.
NB: variable curvalue is dynamically scoped (used in proof-assistant-format).")

(defun proof-assistant-format-bool (value)
  (if value proof-assistant-true-value proof-assistant-false-value))

(defun proof-assistant-format-int (value)
  (funcall proof-assistant-format-int-fn value))

(defun proof-assistant-format-string (value)
  (funcall proof-assistant-format-string-fn value))

   


(provide 'proof-menu)
;; proof-menu.el ends here.
