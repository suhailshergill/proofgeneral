;; proof.el Major mode for proof assistants Copyright (C) 1994,
;; 1995, 1996 LFCS Edinburgh. This version by Dilip Sequeira, by
;; rearranging Thomas Schreiber's code.

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Thanks to David Aspinall, Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens  


;; TO DO:

;; Make lego code buffer local
;; Need to think about fixing up errors caused by pbp-generated commands
;; comments should be replaced by single spaces unless at start of line

(require 'compile)
(require 'comint)
(require 'etags)

(autoload 'w3-fetch "w3" nil t)
(autoload 'easy-menu-define "easymenu")

(defmacro deflocal (var value docstring)
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq var value)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Configuration                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Essentially everything is buffer local, so that we could run multiple
; shells, each with a goals buffer and multiple associated text buffers
; Variable naming convention is that everything which starts with 
; pbp is for the goals buffer, everything which starts proof-shell
; is in the shell buffer, and everything else is in script buffers

(deflocal proof-shell-echo-input t
  "If nil, input to the proof shell will not be echoed")

(deflocal proof-prog-name-ask-p nil
  "*If t, you will be asked which program to run when the inferior
 process starts up.")

(deflocal pbp-change-goal nil
  "*Command to change to the goal %s")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Other buffer-local variables used by proof mode                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These should be set before proof-config-done is called

(deflocal proof-terminal-char nil "terminator character")

(deflocal proof-comment-start nil "Comment start")
(deflocal proof-comment-end nil "Comment end")

;; these should be set in proof-pre-shell-start-hook

(deflocal proof-prog-name nil "program name for proof shell")
(deflocal proof-mode-for-shell nil "mode for proof shell")
(deflocal proof-mode-for-pbp nil "The actual mode for Proof-by-Pointing.")
(deflocal proof-shell-config nil 
  "Function to config proof-system to interface")

(defvar proof-pre-shell-start-hook)
(defvar proof-post-shell-exit-hook)

(deflocal proof-shell-prompt-pattern nil 
   "comint-prompt-pattern for proof shell")

(deflocal proof-shell-init-cmd nil
   "The command for initially configuring the proof process")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Generic config for script management                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-shell-wakeup-char ""
  "A character terminating the prompt in annotation mode")

(deflocal proof-shell-annotated-prompt-string ""
  "Annotated prompt pattern")

(deflocal proof-shell-abort-goal-regexp nil
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(deflocal proof-shell-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.") 

(deflocal proof-shell-proof-completed-regexp nil
  "*Regular expression indicating that the proof has been completed.")

(deflocal proof-shell-result-start ""
  "String indicating the start of an output from the prover following
  a `pbp-goal-command' or a `pbp-hyp-command'.")

(deflocal proof-shell-result-end ""
  "String indicating the end of an output from the prover following a
  `pbp-goal-command' or a `pbp-hyp-command'.") 

(deflocal proof-shell-start-goals-string ""
  "String indicating the start of the proof state.")

(deflocal proof-shell-end-goals-string ""
  "String indicating the end of the proof state.")

(deflocal proof-shell-sanitise t "sanitise output?")

(deflocal pbp-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.") 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Internal variables used by scripting and pbp                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-terminal-string nil 
  "You are not authorised for this information.")

(deflocal proof-re-end-of-cmd nil 
  "You are not authorised for this information.")

(deflocal proof-re-term-or-comment nil 
  "You are not authorised for this information.")

(deflocal proof-locked-ext nil
  "You are not authorised for this information.")

(deflocal proof-queue-ext nil
  "You are not authorised for this information.")

(deflocal proof-mark-ext nil 
  "You are not authorised for this information.")

(deflocal proof-buffer-for-shell nil
  "You are not authorised for this information.")

(deflocal proof-shell-script-buffer nil
  "You are not authorised for this information.")

(deflocal proof-shell-pbp-buffer nil
  "You are not authorised for this information.")

(deflocal pbp-shell-buffer nil
  "You are not authorised for this information.")

(deflocal pbp-script-buffer nil
  "You are not authorised for this information.")

(deflocal proof-shell-busy nil 
  "You are not authorised for this information.")

(deflocal proof-buffer-type nil 
  "You are not authorised for this information.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar running-xemacs  nil)
(defvar running-emacs19 nil)

(setq running-xemacs  (string-match "XEmacs\\|Lucid" emacs-version))
(or running-xemacs
    (setq running-emacs19 (string-match "^19\\." emacs-version)))

;; courtesy of Mark Ruys 
(defun emacs-version-at-least (major minor)
  "Test if emacs version is at least major.minor"
  (or (> emacs-major-version major)
      (and (= emacs-major-version major) (>= emacs-minor-version minor)))
)

(defvar extended-shell-command-on-region
  (emacs-version-at-least 19 29)
  "Does `shell-command-on-region' optionally offer to output in an other buffer?")

;; in case Emacs is not aware of read-shell-command-map
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap)))
    (if (not (fboundp 'set-keymap-parents))
        (setq map (append minibuffer-local-map map))
      (set-keymap-parents map minibuffer-local-map)
      (set-keymap-name map 'read-shell-command-map))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands.")


;; in case Emacs is not aware of the function read-shell-command
(or (fboundp 'read-shell-command)
    ;; from minibuf.el distributed with XEmacs 19.11
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          A couple of small utilities                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun string-to-list (s separator) 
  "converts strings `s' separated by the character `separator' to a
  list of words" 
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))

(defun ids-to-regexp (l)
  "transforms a non-empty list of identifiers `l' into a regular
  expression matching any of its elements"
(mapconcat (lambda (s) (concat "\\<" s "\\>")) l "\\|"))

(defun w3-remove-file-name (address)
  "remove the file name in a World Wide Web address"
  (string-match "://[^/]+/" address)
  (concat (substring address 0 (match-end 0))
          (file-name-directory (substring address (match-end 0)))))

(defun set-queue-prop (property value)
  (set-extent-property proof-queue-ext property value))

(defun get-queue-prop (property)
  (extent-property proof-queue-ext property))

(defun set-locked-prop (property value)
  (set-extent-property proof-locked-ext property value))

(defun get-locked-prop (property)
  (extent-property proof-locked-ext property))

(defun set-extent-start (extent value)
  (set-extent-endpoints extent value (extent-end-position extent)))

(defun set-extent-end (extent value)
  (set-extent-endpoints extent (extent-start-position extent) value))

(defmacro pbp-shell-val (var)
  (list 'save-excursion (list 'set-buffer 'pbp-shell-buffer)
	                var))

(defun proof-end-of-locked ()
  (or (extent-end-position proof-locked-ext) (point-min)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting and stopping the lego shell                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-live-buffer () 
  (if (and proof-buffer-for-shell
	   (comint-check-proc proof-buffer-for-shell))
       proof-buffer-for-shell))

(defun proof-start-shell ()
  (if (proof-shell-live-buffer)
      ()
    (run-hooks 'proof-pre-shell-start-hook)
    (if proof-prog-name-ask-p
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    (let ((proc
	   (concat "Inferior "
		   (substring proof-prog-name
			      (string-match "[^/]*$" proof-prog-name)))))
      (while (get-buffer (concat "*" proc "*"))
	(if (string= (substring proc -1) ">")
	    (aset proc (- (length proc) 2) 
		  (+ 1 (aref proc (- (length proc) 2))))
	  (setq proc (concat proc "<2>"))))

      (message (format "Starting %s process..." proc))

      (let ((prog-name-list (string-to-list proof-prog-name " ")))
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))

      (setq proof-buffer-for-shell (get-buffer (concat "*" proc "*")))

      (let ((shell-mode proof-mode-for-shell) 
            (pbp-mode proof-mode-for-pbp)
	    (shellbuf proof-buffer-for-shell)
	    (scriptbuf (current-buffer)))
	(save-excursion
	  (set-buffer shellbuf)
	  (setq proof-shell-script-buffer scriptbuf)
	  (setq proof-shell-pbp-buffer 
		(get-buffer-create (concat "*" proc "-goals*")))
	  (put 'proof-shell-script-buffer 'permanent-local t) 
	  (put 'proof-shell-pbp-buffer 'permanent-local t)
	  (funcall shell-mode)
	  (set-buffer proof-shell-pbp-buffer)
	  (funcall pbp-mode)
	  (setq pbp-shell-buffer shellbuf)
	  (setq pbp-script-buffer scriptbuf)))

      (message 
       (format "Starting %s process... done." proc)))))
  

(defun proof-stop-shell ()
  "Exit the PROOF process

  Runs proof-shell-exit-hook if non nil"

  (interactive)
  (save-excursion
    (let ((buffer (proof-shell-live-buffer)) (proc))
      (if buffer
	  (progn
	    (save-excursion
	      (set-buffer buffer)
	      (setq proc (process-name (get-buffer-process)))
	      (comint-send-eof)
	      (save-excursion
		(set-buffer proof-shell-script-buffer)
		(detach-extent proof-queue-ext))
	      (kill-buffer))
	    (run-hooks 'proof-shell-exit-hook)

             ;;it is important that the hooks are
	     ;;run after the buffer has been killed. In the reverse
	     ;;order e.g., intall-shell-fonts causes problems and it
	     ;;is impossilbe to restart the PROOF shell

	    (message (format "%s process terminated." proc)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Proof by pointing                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst pbp-goal-command "Pbp %s;"
  "Command informing the prover that `pbp-button-action' has been
  requested on a goal.")


(defconst pbp-hyp-command "PbpHyp %s;"
  "Command informing the prover that `pbp-button-action' has been
  requested on an assumption.")

(defvar pbp-keymap (make-keymap 'Pbp-keymap) 
  "Keymap for proof mode")

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))

(define-key pbp-keymap 'button2 'pbp-button-action)

; Using the extents in a mouse behavior is quite simple: from the
; mouse position, find the relevant extent, then get its annotation
; and produce a piece of text that will be inserted in the right
; buffer.  Attaching this behavior to the mouse is simply done by
; attaching a keymap to all the extents.

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l) 
      (setq ls (cons (int-to-string (aref string a)) 
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun pbp-construct-command ()
  (let* ((ext (extent-at (point) () 'proof))
	 (top-ext (extent-at (point) () 'proof-top-element))
	 (top-info (extent-property top-ext 'proof-top-element)) 
	 path cmd)
    (if (extentp top-ext)
	(cond 
	 ((extentp ext)
	  (setq path (concat (cdr top-info)
			     (proof-expand-path (extent-property ext 'proof))))
	  (setq cmd
		(if (eq 'hyp (car top-info))
		    (format pbp-hyp-command path)
		  (format pbp-goal-command path)))
	  (pop-to-buffer pbp-script-buffer)
	  (proof-invisible-command cmd))
	 (t
	  (if (eq 'hyp (car top-info))
	      (progn
		(setq cmd (format pbp-hyp-command (cdr top-info)))
		(pop-to-buffer pbp-script-buffer)
		(proof-invisible-command cmd))
	      (setq cmd (format pbp-change-goal (cdr top-info)))
	      (pop-to-buffer pbp-script-buffer)
	      (proof-insert-pbp-command cmd)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Turning annotated output into pbp goal set              ;;
;;          All very lego-specific at present                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-shell-first-special-char nil "where the specials start")
(deflocal proof-shell-goal-char nil "goal mark")
(deflocal proof-shell-start-char nil "annotation start")
(deflocal proof-shell-end-char nil "annotation end")
(deflocal proof-shell-field-char nil "annotated field end")
(deflocal proof-shell-eager-annotation-start nil "eager ann. field start")
(deflocal proof-shell-eager-annotation-end nil "eager ann. field end")

(defconst proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

(defconst proof-shell-goal-regexp nil
  "A regular expressin matching the identifier of a goal.")

(defconst proof-shell-noise-regexp nil
  "Unwanted information output from the proof process within
  `proof-start-goals-string' and `proof-end-goals-string'.")

(defun pbp-make-top-extent (start end)
  (let (extent name)
    (goto-char start)
    (setq name (cond 
		((looking-at proof-shell-goal-regexp)
		 (cons 'goal (match-string 1)))
		((looking-at proof-shell-assumption-regexp)
		 (cons 'hyp (match-string 1)))))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq extent (make-extent start (point)))
    (set-extent-property extent 'mouse-face 'highlight)
    (set-extent-property extent 'keymap pbp-keymap)
    (set-extent-property extent 'proof-top-element name)))

(defun proof-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x )) c ext)
      (while (< ip l)
	(setq c (aref string ip))
	(if (< c proof-shell-first-special-char)
	    (progn (aset out op c)
		   (incf op))
	  (cond 
	   ((= c proof-shell-goal-char)
	    (setq topl (append topl (list (+ 1 op)))))
	   ((= c proof-shell-start-char)	    
	    (setq ap (- (aref string (incf ip)) 32))
	    (incf ip)
	    (while (not (= (aref string ip) proof-shell-end-char))
	      (aset ann ap (- (aref string ip) 32))
	      (incf ap)
	      (incf ip))
	    (setq stack (cons op (cons (substring ann 0 ap) stack))))
	   ((= c proof-shell-field-char)
	    (setq ext (make-extent (car stack) op out))
	    (set-extent-property ext 'mouse-face 'highlight)
	    (set-extent-property ext 'keymap pbp-keymap)
	    (set-extent-property ext 'proof (cadr stack))
	    (set-extent-property ext 'duplicable t)
	    (setq stack (cddr stack)))))
	(incf ip))
      (display-buffer (set-buffer proof-shell-pbp-buffer))
      (erase-buffer)
      (insert (substring out 0 op))
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-extent ip (car topl)))
      (pbp-make-top-extent ip (point-max)))))

(defun proof-shell-strip-annotations (string)
  (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
    (while (< ip l)
      (if (>= (aref string ip) proof-shell-first-special-char)
	  (if (char-equal (aref string ip) proof-shell-start-char)
	      (progn (incf ip)
		     (while (< (aref string ip) proof-shell-first-special-char)
		       (incf ip))))
	(aset out op (aref string ip))
	(incf op))
      (incf ip))
    (substring out 0 op)))

(defun proof-shell-handle-error (cmd string)
  (save-excursion 
    (display-buffer (set-buffer proof-shell-pbp-buffer))
    (goto-char (point-max))
    (if (re-search-backward pbp-error-regexp nil t) 
	(delete-region (- (point) 2) (point-max)))
    (newline 2)
    (insert-string string)
    (beep))
  (set-buffer proof-shell-script-buffer)
  (detach-extent proof-queue-ext)
  (mapcar-extents 'delete-extent nil (current-buffer) 
		  (proof-end-of-locked) (point-max) nil 'type)
  (proof-release-process))

(deflocal proof-shell-delayed-output nil
  "The last interesting output the proof process output, and what to do
   with it.")

(defun proof-shell-handle-delayed-output ()
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (display-buffer proof-shell-pbp-buffer)
    (save-excursion
      (cond 
       ((eq ins 'insert)
	(setq str (proof-shell-strip-annotations str))
	(set-buffer proof-shell-pbp-buffer)
	(insert str))
       ((eq ins 'analyse)
	(proof-shell-analyse-structure str))
       (t (set-buffer proof-shell-pbp-buffer)
	  (insert "\n\nbug???")))))
  (setq proof-shell-delayed-output (cons 'insert "done")))


(defun proof-shell-process-output (cmd string)
  (cond 
   ((string-match proof-shell-error-regexp string)
    (cons 'error (proof-shell-strip-annotations string)))

   ((string-match proof-shell-abort-goal-regexp string)
    (setq proof-shell-delayed-output (cons 'insert "\n\nAborted"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (setq proof-shell-delayed-output
	  (cons 'insert (concat "\n" (match-string 0 string)))))

   ((string-match proof-shell-start-goals-string string)
    (let (start end)
      (while (progn (setq start (match-end 0))
		    (string-match proof-shell-start-goals-string 
				  string start)))
      (string-match proof-shell-end-goals-string string start)
      (setq proof-shell-delayed-output 
	    (cons 'analyse (substring string start end)))))
       
   ((string-match proof-shell-result-start string)
    (let (start end)
      (setq start (+ 1 (match-end 0)))
      (string-match proof-shell-result-end string)
      (setq end (- (match-beginning 0) 1))
      (cons 'loopback (substring string start end))))
   
   ((and (>= (length cmd) 6) (string= "Module" (substring cmd 0 6)))
    (setq proof-shell-delayed-output (cons 'insert "Imports done!")))

   (t (setq proof-shell-delayed-output (cons 'insert string)))))
         
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Low-level commands for shell communication                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-insert (string)
  (goto-char (point-max))
  (insert (funcall proof-shell-config) string)
  (if (not (extent-property proof-mark-ext 'detached))
      (set-extent-endpoints proof-mark-ext (point) (point)))
  (comint-send-input))

(defun proof-send (string)
  (let ((l (length string)) (i 0))
    (while (< i l)
      (if (= (aref string i) ?\n) (aset string i ?\ ))
      (incf i)))
  (save-excursion
    (set-buffer proof-buffer-for-shell)
    (proof-shell-insert string)))

;; grab the process and return t, otherwise return nil. Note that this
;; is not really intended for anything complicated - just to stop the
;; user accidentally sending a command while the queue is running.

(defun proof-check-process-available ()
  (save-excursion
    (if (proof-shell-live-buffer)
	(progn (set-buffer proof-buffer-for-shell)
	       (if proof-shell-busy (error "Proof Process Busy!"))))))

(defun proof-grab-process ()
  (save-excursion
    (proof-start-shell)
    (let ((buf (current-buffer)))
      (set-buffer proof-buffer-for-shell)
      (if proof-shell-busy	       
	  (error "proof process busy")
	(if (not (eq proof-shell-script-buffer buf))
	    (error "Bug: Don't own process") 
	  (setq proof-shell-busy t)
	  t)))))

(defun proof-release-process ()
  (if (proof-shell-live-buffer)
      (save-excursion
	(let ((buf (current-buffer)))
	  (set-buffer proof-buffer-for-shell)
	  (if (not proof-shell-busy)
	      (error "Bug: Proof process not busy")
	    (if (not (eq proof-shell-script-buffer buf)) 
		(error "Bug: Don't own process")
	      (setq proof-shell-busy nil)))))))

(defun proof-start-queue (start end alist &optional obj)
  (proof-grab-process) ; TODO: catch error and delete extents in queue
  (save-excursion
    (set-buffer proof-buffer-for-shell)
    (erase-buffer proof-shell-pbp-buffer))
  (setq proof-shell-delayed-output (cons 'insert "Done."))
  (if (null obj) (setq obj (current-buffer)))
  (set-extent-endpoints proof-queue-ext start end obj)
  (set-queue-prop 'action-list alist)
  (proof-send (cadar alist)))

; returns t if it's run out of input

(defun proof-shell-exec-loop ()
  (save-excursion
    (set-buffer proof-shell-script-buffer)
    (let* ((a (get-queue-prop 'action-list))
	   (ext (caar a))
	   (act (caddar a)))
      (if (null act) (error "BUG2"))
      (funcall act ext)
      (setq a (cdr a))
      (set-queue-prop 'action-list a)
      (if (null a)
	  (progn (proof-release-process)
		 (detach-extent proof-queue-ext)
		 t)
	(proof-send (cadar a))
	()))))

(defun proof-shell-insert-loopback-cmd (cmd)
  (save-excursion
    (set-buffer proof-shell-script-buffer)
    (let (start ext ls)
      (goto-char (setq start (proof-end-of-locked)))
      (insert cmd)
      (setq ext (make-extent start (point)))
      (set-extent-property ext 'type 'pbp)
      (set-extent-property ext 'cmd cmd)
      (setq ls (get-queue-prop 'action-list))
      (set-extent-endpoints proof-queue-ext start (point) (current-buffer))
      (set-queue-prop 'action-list 
		      (cons (car ls) 
			    (cons (list ext cmd 'proof-done-advancing)
				  (cdr ls)))))))

(defun proof-shell-popup-eager-annotation ()
  (let (mrk str)
    (save-excursion 
      (goto-char (point-max))
      (search-backward proof-shell-eager-annotation-start)
      (setq mrk (+ 1 (point)))
      (search-forward proof-shell-eager-annotation-end)
      (setq str (buffer-substring mrk (- (point) 1)))
      (display-buffer (set-buffer proof-shell-pbp-buffer))
      (insert str "\n"))))
      
(defun proof-shell-filter (str) 
  (if (string-match proof-shell-eager-annotation-end str)
      (proof-shell-popup-eager-annotation))
  (if (string-match proof-shell-wakeup-char str)
      (if (extent-property proof-mark-ext 'detached)
	  (progn
	    (goto-char (point-min))
	    (search-forward proof-shell-annotated-prompt-string)
	    (set-extent-endpoints proof-mark-ext (point) (point))
	    (backward-delete-char 1))
	(let (string mrk res cmd)	
	    (goto-char (setq mrk (extent-start-position proof-mark-ext)))
	    (search-forward proof-shell-annotated-prompt-string nil t)
	    (set-extent-endpoints proof-mark-ext (point) (point))
	    (backward-char (length proof-shell-annotated-prompt-string))
	    (setq string (buffer-substring mrk (point)))
	    (if proof-shell-sanitise 
		(progn
		  (delete-region mrk (point))
		  (insert (proof-shell-strip-annotations string))))
	    (goto-char (extent-start-position proof-mark-ext))
	    (backward-delete-char 1)
	    (save-excursion
	      (set-buffer proof-shell-script-buffer)
	      (setq cmd (cadar (get-queue-prop 'action-list))))
	    (save-excursion
	      (setq res (proof-shell-process-output cmd string))
	      (cond
	       ((and (consp res) (eq (car res) 'error))
		(proof-shell-handle-error cmd (cdr res)))
	       ((and (consp res) (eq (car res) 'loopback))
		(proof-shell-insert-loopback-cmd (cdr res))
		(proof-shell-exec-loop))
	       (t (if (proof-shell-exec-loop)
		      (proof-shell-handle-delayed-output)))))))))
	    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Script management                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
; Script management uses two major extents: Locked, which marks text
; which has been sent to the proof assistant and cannot be altered
; without being retracted, and Queue, which contains stuff being
; queued for processing.  Queue has a property 'action-list' which
; contains a list of (extent,command,action) triples. The loop looks
; like: Execute the command, and if it's successful, do action on
; extent.  If the command's not successful, we bounce the rest of the
; queue and do some error processing.
;
; 'goalsave - denoting a 'goalsave pair in the locked region
;    a 'goalsave region has a 'name property which is the name of the goal
; 'pbp - denoting an extent created by pbp
; 'vanilla - denoting any other extent.
;   'pbp & 'vanilla extents have a property 'cmd, which says what lego
;   command they contain. 

; We don't allow commands while the queue has anything in it.  So we
; do configuration by concatenating the config command on the front in
; proof-send

(defun proof-done-invisible (ext) ())

(defun proof-invisible-command (cmd)
  (proof-check-process-available)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue 0 (length cmd) 
		     (list (list (make-extent 0 (length cmd) cmd) cmd
				 'proof-done-invisible))
		     cmd))

(defun proof-insert-pbp-command (cmd)
  (proof-check-process-available)
  (let (start ext)
    (goto-char (setq start (proof-end-of-locked)))
    (insert cmd)
    (setq ext (make-extent start (point)))
    (set-extent-property ext 'type 'pbp)
    (set-extent-property ext 'cmd cmd)
    (proof-start-queue start (point) (list (list ext cmd 
						 'proof-done-advancing)))))

(defun proof-done-advancing (ext)
  (let ((end (extent-end-position ext)) cmd nam gext next)
    (set-extent-endpoints proof-locked-ext 1 end)
    (set-extent-start proof-queue-ext end)
    (setq cmd (extent-property ext 'cmd))
    (if (or (< (length cmd) 4) (not (string= "Save" (substring cmd 0 4))))
	(set-extent-property ext 'highlight 'mouse-face)
      (if (string-match 
	   "\\(Save\\|SaveFrozen\\|SaveUnfrozen\\)\\s-+\\([^;]+\\)" cmd)
	  (setq nam (match-string 2 cmd)))
      (setq gext ext)
      (while (progn (setq cmd (extent-property gext 'cmd))
		    (not (string= "Goal" (substring cmd 0 4))))
	(setq next (extent-at (extent-start-position gext) nil 
			      'type nil 'before))
	(delete-extent gext)
	(setq gext next))
      (if (null nam)
	  (if (string-match "Goal\\s-+\\([^:]+\\)" cmd)
	      (setq nam (match-string 1 cmd))
 	    (error "Oops... can't find Goal name!!!")))
      (set-extent-end gext end)
      (set-extent-property gext 'highlight 'mouse-face)
      (set-extent-property gext 'type 'goalsave)
      (set-extent-property gext 'name nam))))

; Create a list of (int,string) pairs from the end of the locked
; region to pos, denoting the command and the position of its
; terminator. Return 'comment consed on the front if we're inside a
; comment

(defun proof-segment-up-to (pos)
  (save-excursion
    (let ((str (make-string 5000 ?x)) 
	  (i 0) (depth 0) done alist c)
      (goto-char (proof-end-of-locked))
      (while (not done)
	(cond 
	 ((and (= (point) pos) (> depth 0))
	  (setq done t alist (append alist (list 'comment))))
	 ((= (point) (point-max))
	  (setq done t))
	 ((looking-at "\\*)")
	  (if (= depth 0) 
	      (progn (message "Warning: extraneous comment end") (setq done t))
	    (setq depth (- depth 1)) (forward-char 2)))
	 ((looking-at "(\\*")
	  (setq depth (+ depth 1)) (forward-char 2))
	 ((> depth 0) (forward-char))
	 (t
	  (setq c (char-after (point)))
	  (if (or (> i 0) (not (= (char-syntax c) ?\ )))
	      (progn (aset str i c) (setq i (+ 1 i))))	  
	  (forward-char)
	  (if (= c ?\;)
	      (progn 
		(setq alist (cons (list (substring str 0 i) (point)) alist))
		(if (>= (point) pos) (setq done t) (setq i 0)))))))
      (nreverse alist))))

(defun proof-semis-to-vanillas (semis)
  (let ((ct (proof-end-of-locked)) ext alist cmd)
    (while (not (null semis))
      (setq ext (make-extent ct (cadar semis))
            cmd (caar semis)
	    ct (cadar semis))
      (set-extent-property ext 'type 'vanilla)
      (set-extent-property ext 'cmd cmd)
      (setq alist (cons (list ext cmd 'proof-done-advancing) alist))
      (setq semis (cdr semis)))
    (nreverse alist)))

(defun proof-assert-until-point ()
  (interactive)
  (proof-check-process-available)
  (if (not (eq proof-buffer-type 'script))
      (error "Must be running in a script buffer"))
  (if (not (re-search-backward "\\S-" (proof-end-of-locked) t))
      (error "Nothing to do!"))
  (let (semis)			 
    (setq semis (proof-segment-up-to (point)))
    (if (or (null semis) (eq semis (list 'comment))) (error "Nothing to do!"))
    (if (eq 'comment (car semis)) (setq semis (cdr semis)))
    (goto-char (cadar (last semis)))
    (proof-start-queue (proof-end-of-locked) (point)
		       (proof-semis-to-vanillas semis))))
    
(defun proof-done-retracting (ext)
  (let ((start (extent-start-position ext))
        (end (extent-end-position ext)))
    (set-extent-end proof-locked-ext start)
    (set-extent-end proof-queue-ext start)
    (mapcar-extents 'delete-extent nil (current-buffer) start end  nil 'type)
    (delete-extent ext)))

(deflocal lego-undoable-commands-regexp
  (ids-to-regexp '("Refine" "Intros" "intros" "Next" "Qrepl" "Claim" "Equiv"
		   "For" "Repeat" "Succeed" "Fail" "Try" "Assumption" "UTac"
		   "Qnify" "AndE" "AndI" "exE" "exI" "orIL" "orIR" "orE"
		   "ImpI" "impE" "notI" "notE" "allI" "allE")) "Undoable list")

(defun lego-count-undos (sext)
  (let ((ct 0) str i)
    (while sext
      (setq str (extent-property sext 'cmd))
      (if (eq (extent-property sext 'type) 'vanilla)
	(if (string-match
	     "Refine\\|Intros\\|intros\\|Next\\|Qrepl\\|Claim\\|Equiv\\|For\\|Repeat\\|Succeed\\|Fail\\|Try\\|" str)
	    (setq ct (+ 1 ct)))
	(setq i 0)
	(while (< i (length str)) 
	  (if (= (aref str i) ?\;) (setq ct (+ 1 ct)))
	  (setq i (+ 1 i))))
      (setq sext (extent-at (extent-end-position sext) nil 'type nil 'after)))
  (concat "Undo " (int-to-string ct) ";")))

(defun lego-find-and-forget (sext) 
  (let (str ans)
    (while sext
      (if (eq (extent-property sext 'type) 'goalsave)
	  (setq ans (concat "Forget " (extent-property sext 'name) ";")
		sext nil)
	(setq str (extent-property sext 'cmd))
	(cond
	 ((string-match "\\`\\s-*\\[\\s-*\\(\\w+\\)\\s-*[:=]" str)
	  (setq ans (concat "Forget " (match-string 1 str) ";")
		sext nil))

	 ((string-match "\\`Inductive\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	  (setq ans (concat "Forget " (match-string 1 str) ";")
		sext nil))

	 ((string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	  (setq ans (concat "ForgetMark " (match-string 1 str) ";")
		sext nil))
	 (t 
	  (setq sext 
		(extent-at (extent-end-position sext) nil 'type nil 
			   'after))))))
    (or ans "echo \"Nothing more to Forget.\";")))

(defun proof-retract-until-point ()
  (interactive)
  (proof-check-process-available)
  (if (not (eq proof-buffer-type 'script))
      (error "Must be running in a script buffer"))
  (let ((sext (extent-at (point) nil 'type))
	(end (extent-end-position proof-locked-ext))
	ext start actions done)
    (if (null end) (error "No locked region"))
    (if (or (null sext) (< end (point))) (error "Outside locked region"))
    (setq start (extent-start-position sext))
    
    (setq ext (extent-at end nil 'type nil 'before))
    (while (and ext (not done))		  
      (cond 
       ((eq (extent-property ext 'type) 'goalsave)
	(setq done t))
       ((string= (substring (extent-property ext 'cmd) 0 4) "Goal")
	(setq done 'goal))
       (t
	(setq ext (extent-at (extent-start-position ext) nil
			     'type nil 'before)))))
    (if (eq done 'goal) 
	(if (< (extent-end-position ext) (point))
	    (setq actions (list (list (make-extent start end)
				      (lego-count-undos sext)
				      'proof-done-retracting))
		  end start)
	  (setq actions (list (list (make-extent (extent-start-position ext) 
						 end)
				    "KillRef;" 'proof-done-retracting))
		end (extent-start-position ext))))
    (if (> end start) 
	(setq actions (append actions (list 
				       (list (make-extent start end) 
					     (lego-find-and-forget sext)
					     'proof-done-retracting)))))
    (proof-start-queue (min start end)
		       (extent-end-position proof-locked-ext)
		       actions)))

(defun proof-restart-script ()
  (interactive)
  (if (not (eq proof-buffer-type 'script))
      (error "Restart in script buffer"))
  (mapcar-extents 'delete-extent nil 
		  (current-buffer) (point-min)  (point-max) nil 'type)
  (detach-extent proof-locked-ext)
  (detach-extent proof-queue-ext)
  (if (get-buffer proof-buffer-for-shell) 
      (progn
	(save-excursion 
	  (set-buffer proof-buffer-for-shell)
	  (setq proof-shell-busy nil)
	  (if (get-buffer proof-shell-pbp-buffer)
	      (kill-buffer proof-shell-pbp-buffer)))
	(kill-buffer proof-buffer-for-shell))))
	  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-active-terminator-minor-mode nil 
"active terminator minor mode flag")

(make-variable-buffer-local 'proof-active-terminator-minor-mode)
(put 'proof-active-terminator-minor-mode 'permanent-local t)

(defun proof-active-terminator-minor-mode (&optional arg)
  "Toggle PROOF's Active Terminator minor mode.
With arg, turn on the Active Terminator minor mode if and only if arg
is positive.

If Active terminator mode is enabled, a terminator will process the
current command."

 (interactive "P")
 
;; has this minor mode been registered as such?
  (or (assq 'proof-active-terminator-minor-mode minor-mode-alist)
      (setq minor-mode-alist
            (append minor-mode-alist
                    (list '(proof-active-terminator-minor-mode " ;")))))

 (setq proof-active-terminator-minor-mode
        (if (null arg) (not proof-active-terminator-minor-mode)
          (> (prefix-numeric-value arg) 0)))
   (if (fboundp 'redraw-modeline) (redraw-modeline) (redraw-modeline)))

(defun proof-active-terminator ()
  (interactive)
  (if proof-active-terminator-minor-mode 
      (proof-process-active-terminator)
    (self-insert-command 1)))

(defun proof-process-active-terminator ()
  (proof-check-process-available)
  (let ((mrk (point)) ins semis)
    (if (looking-at "\\s-")
	  (if (not (re-search-backward "\\S-" (proof-end-of-locked) t))
	      (error "Nothing to do!")))
    (if (not (= (char-after (point)) ?\;))
	(progn (forward-char) (insert ";") (setq ins t)))
    (setq semis (proof-segment-up-to (point)))    
    (if (null semis) (error "Nothing to do!"))
    (if (eq 'comment (car semis)) 
	(progn (if ins (backward-delete-char 1)) (goto-char mrk) (insert ";"))
      (goto-char (cadar (last semis)))
      (proof-start-queue (proof-end-of-locked) (point)
			 (proof-semis-to-vanillas semis)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; font lock faces: declarations, errors, tacticals                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar font-lock-declaration-name-face 
(progn 
  (cond ((eq (device-class) 'color)
	 ;notice that device-class does not exist in Emacs 19.30

	 (copy-face 'bold 'font-lock-declaration-name-face)

	 ;; Emacs 19.28 compiles this down to
	 ;; internal-set-face-1. This is not compatible with XEmacs
	 (dont-compile
	   (set-face-foreground
	    'font-lock-declaration-name-face "chocolate")))
	(t (copy-face 'bold-italic 'font-lock-declaration-name-face)))
  (if running-emacs19
      (setq font-lock-declaration-name-face
	    (face-name 'font-lock-declaration-name-face)))))

(defvar font-lock-tacticals-name-face
(if (eq (device-class) 'color)
    (let ((face (make-face 'font-lock-tacticals-name-face)))
      (dont-compile
	(set-face-foreground face
			     "MediumOrchid3"))
      face)
  (copy-face 'bold 'font-lock-tacticals-name-face)))

(defvar font-lock-error-face
(if (eq (device-class) 'color)
    (let ((face (make-face 'font-lock-error-face)))
      (dont-compile
	(set-face-foreground face
			     "red"))
      face)
  (copy-face 'bold 'font-lock-error-face)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof mode configuration                                         ;;
;; Eventually there will be some more                               ;;
;; functionality here common to both coq and lego.                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-derived-mode proof-mode fundamental-mode 
  "Proof" "Proof mode - not standalone"
  (setq proof-buffer-type 'script)
  (setq proof-queue-ext (make-extent nil nil (current-buffer)))
  (setq proof-locked-ext (make-extent nil nil (current-buffer)))
  (set-queue-prop 'start-closed t)
  (set-queue-prop 'end-open t)
  (set-queue-prop 'read-only t)
  (make-face 'proof-queue-face)
  (set-face-background 'proof-queue-face "mistyrose")
  (set-queue-prop 'face 'proof-queue-face)
  
  (set-locked-prop 'start-closed t)
  (set-locked-prop 'end-open t)
  (set-locked-prop 'read-only t)
  (make-face 'proof-locked-face)
  (set-face-background 'proof-locked-face "lavender")
  (set-locked-prop 'face 'proof-locked-face)
  (make-local-hook 'proof-pre-shell-start-hook)
  (make-local-hook 'proof-shell-exit-hook)

)

;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 

;; calculate some strings and regexps for searching

  (setq proof-terminal-string (char-to-string proof-terminal-char))

  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-comment-end))
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat (regexp-quote proof-comment-start) "+\\s_?"))

  (setq proof-re-end-of-cmd (concat "\\s_*" proof-terminal-string "\\s_*\\\'"))
  (setq proof-re-term-or-comment 
	(concat proof-terminal-string "\\|" (regexp-quote proof-comment-start)
		"\\|" (regexp-quote proof-comment-end)))

  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map proof-terminal-char 'proof-active-terminator)
  (define-key proof-mode-map "\C-ca"    'proof-assert-until-point)
  (define-key proof-mode-map "\C-cu"    'proof-retract-until-point)

  )

(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof shell mode - not standalone"
  (setq proof-buffer-type 'shell)
  (setq proof-shell-busy nil)
  (setq proof-shell-sanitise t)
  (setq proof-shell-delayed-output (cons 'insert "done"))
  (setq comint-prompt-regexp proof-shell-prompt-pattern)
  (and running-emacs19 (setq comint-scroll-show-maximum-output t))
  (add-hook 'comint-output-filter-functions 'proof-shell-filter t)
  (setq comint-append-old-input nil)
  (setq proof-mark-ext (make-extent nil nil (current-buffer)))
  (set-extent-property proof-mark-ext 'detachable nil)
  (set-extent-property proof-mark-ext 'start-closed t)
  (set-extent-property proof-mark-ext 'end-open t))

(defun proof-shell-config-done ()
  (accept-process-output (get-buffer-process (current-buffer)))
  (proof-shell-insert proof-shell-init-cmd)
  (while (extent-property proof-mark-ext 'detached)
    (if (accept-process-output (get-buffer-process (current-buffer)) 5)
	()
      (error "Failed to initialise proof process"))))

(define-derived-mode pbp-mode fundamental-mode 
  (setq proof-buffer-type 'pbp)
  "Proof" "Proof by Pointing"
  (suppress-keymap pbp-mode-map)
  (erase-buffer))

(provide 'proof)
