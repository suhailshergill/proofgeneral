;;; tree-tree.el --- Proof General prooftree communication.
;;
;; Copyright (C) Hendrik Tews
;; Authors:   Hendrik Tews
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;; Commentary:
;;
;; Generic code for the communication with prooftree. Prooftree
;; is an ocaml-gtk program that visualizes proof trees.
;;
;; The main problem with proof tree visualization is that Coq (and
;; probably other proof assistants as well) does not provide any
;; information about which subgoals are new and have been created by
;; the last proof command and which subgoals stem from older proof
;; commands.
;;
;; To solve this problem prooftree relies on unique identification
;; strings of goals, which are called goal or sequent ID's in the
;; code. With these ID's it is easy to keep track which goals are new.
;;
;; A second problem is that, for an undo command, Coq (and probably
;; other proof assistants as well) does not tell which subgoals and
;; which finished branches must be deleted. Therefore prooftree needs
;; a continuously increasing proof state number and keeps a complete
;; undo history for every proof.
;;
;; A third problem is that Coq (and probably other proof assistants as
;; well) is not able to generate the information for a proof tree in
;; the middle of a proof. Therefore, if the user wants to start the
;; proof-tree display in the middle of the proof, it is necessary to
;; retract to the start of the proof and then to reassert to the
;; previous end of the locked region. This raises another issue with
;; Proof General. Namely that the locked region is maintained in the
;; delayed output processing. Therefore one cannot simply retract and
;; reassert in one function. After retracing it is necessary to let
;; Emacs idle, because it must first process the delayed part of the
;; undo command before reasserting is possible.
;; 
;; The design of prooftree (the visualization program), the glue code
;; inside Proof General (mostly in this file) and the communication
;; protocol tries to achieve the following two goals:
;;
;;   * Functionality is preferably transferred into prooftree, because
;;     this is written in Ocaml, which I am more fluent with.
;;
;;   * An exception is regular expression matching, which I find
;;     easier in Emacs lisp.
;;
;;   * To avoid synchronization trouble the communication between
;;     Proof General and prooftree is one way: Only Proof General
;;     sends display or undo command to prooftree. Prooftree does only
;;     print welcome or error messages. This goal requires that some
;;     of the heuristics, which decide which subgoals are new, need to
;;     be implemented here.
;;
;; In general the glue code here works on the delayed output. That is,
;; the glue code here runs when the next proof command has already
;; been sent to the proof assistant. The glue code makes a light
;; analysis on the output of the proof assistant, extracts the
;; necessary parts with regular expressions and sends appropriate
;; commands to prooftree. This is achieved by calling the main entry
;; here, the function `proof-tree-handle-delayed-output' from the
;; proof shell filter function after `proof-shell-exec-loop' has
;; finished.
;;
;; However, some aspects can not be delayed. Those are treated by
;; `proof-tree-urgent-action'. Its primary use is for inserting
;; special goal-displaying commands into `proof-action-list' before
;; the next real proof command runs. For Coq this needs to be done for
;; newly generated subgoals and for goals that contain an existential
;; variable that got instantiated in the last proof step.
;;
;;
;; Todo:
;;   - display toggle menu and toolbar entry

;;; Code:

(require 'cl)

(eval-when (compile)
  (require 'proof-shell))


;;
;; User options
;;

(defgroup proof-tree ()
  "Customization for the proof tree visualizer"
  :group 'proof-general
  :package-version '(ProofGeneral . "4.X"))

(defcustom proof-tree-program (proof-locate-executable "prooftree" t nil)
  "Command to invoke prooftree."
  :type 'string
  :group 'proof-tree)

(defcustom proof-tree-arguments ()
  "Command line arguments for prooftree."
  :type '(repeat string)
  :group 'proof-tree)


;;
;; Proof assistant options
;;

(defgroup proof-tree-internals ()
  "Proof assistant specific customization of prooftree."
  :group 'proof-general-internals
  :package-version '(ProofGeneral . "4.X"))

(defcustom proof-tree-ignored-commands-regexp nil
  "Commands that should be ignored for the prooftree display.
The output of commands matching this regular expression is not
send to prooftree. It should match commands that display
additional information but do not make any proof progress."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-navigation-command-regexp nil
  "Regexp to match a navigation command.
A navigation command typically focusses on a different open goal
without changing any of the open goals."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-current-goal-regexp nil
  "Regexp to match the current goal and its ID.
The regexp is matched against the output of the proof assistant
to extract the current goal with its ID. The regexp must have 2
grouping constructs, the first one matches just the ID, the
second one the complete sequent text that is to be sent to
prooftree."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-update-goal-regexp nil
  "Regexp to match a goal and its ID.
The regexp is matched against the output of additional show-goal
commands inserted by Proof General. Proof General inserts such
commands to update the goal text in prooftree. This is necessary,
for instance, when existential variables get instantiated."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-additional-subgoal-ID-regexp nil
  "Regular expression to match ID's of additional subgoals.
This regexp is used to extract the ID's of all additionally open
goals. The regexp is used in a while loop and must match one
subgoal ID with subgroup 1."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-existential-regexp nil
  "Regexp to match existential variables.
Existential variables exist for instance in Isabelle/Hol and in
Coq. They are placeholders for terms that might (for Coq they
must) get instantiated in a later stage of the proof. This regexp
should match one existential variable in subgroup 1. It is used
inside a while loop to extract all existential variables from the goal text.

Leave this variable at nil for proof assistants that do not have
existential variables."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-proof-completed-regexp nil
  "Regexp to match the proof-is-complete message."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-get-proof-info nil
  "Proof assistant specific function for information about the current proof.
This function must take two arguments, the command and the flags
as they occur in the item of `proof-action-list' that produced
the current output. This function must return a list, which
contains in the following order:

* the current state number (as positive integer)
* the name of the current proof (as string)

The state number is used to implement undo in prooftree. The
proof name is used to distinguish different proofs inside
prooftree."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-extract-instantiated-existentials nil
  "Proof assistant specific function for instantiated existential variables.
This function should return the list of currently instantiated
existential variables as a list of strings. The function is
called with the `proof-shell-buffer' as current buffer and with
two arguments start and stop, which designate the region
containing the last output from the proof assistant.

Depending on the distribution of existential variables the
function `proof-tree-show-sequent-command' might be called
shortly afterwards. Therefore
`proof-tree-extract-instantiated-existentials' can setup a cache
for `proof-tree-show-sequent-command'."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-show-sequent-command nil
  "Proof assistant specific function for a show-goal command.
This function is applied to an ID of a goal and should return a
command (as string) that will display the complete sequent with
that ID. The regexp `proof-tree-update-goal-regexp' should match
the output of the proof assistant for the returned command, such
that `proof-tree-update-sequent' will update the sequent ID
inside prooftree.

If the proof assistant is unable to redisplay sequent ID the
function should return nil and prooftree will not get updated.

This function is called after
`proof-tree-extract-instantiated-existentials', so it can reuse
information computed there."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-urgent-action-hook ()
  "Normal hook for prooftree actions that cannot be delayed.
This hook is called (indirectly) from inside
`proof-shell-exec-loop' after the preceeding command has been
choped off `proof-action-list' and before the next command is
sent to the proof assistant. This hook can therefore be used to
insert additional commands into `proof-action-list' that must be
executed before the next real proof command.

If `proof-tree-extract-instantiated-existentials' is called then
it is called before this hook. However, if there are currently no
uninstantiated existential variables, then the call to
`proof-tree-extract-instantiated-existentials' might be skipped.

This hook is used, for instance, for Coq to insert Show commands
for newly generated subgoals. (The normal Coq output does not
contain the complete sequent text of newly generated subgoals.)"
  :type 'hook
  :group 'proof-tree-internals)


;;
;; Internal variables
;;

(defvar proof-tree-external-display nil
  "Display proof trees in external prooftree windows if t.
Controlled by `proof-tree-external-display-toggle'.")

(defvar proof-tree-process nil
  "Emacs lisp process object of the prooftree process.")

(defconst proof-tree-process-name "proof-tree"
  "Name of the prooftree process for Emacs lisp.")

(defconst proof-tree-process-buffer
  (concat "*" proof-tree-process-name "*")
  "Buffer for stdout and stderr of the prooftree process.")

(defvar proof-tree-last-state 0
  "Last state of the proof assistant.
Used for undoing in prooftree.")

(defvar proof-tree-current-proof nil
  "Name and start pos of the current proof or nil if there is none.
This variable is used for `proof-tree-external-display-toggle' to
display the proof tree of the current proof. It is further used
to display a warning when the user starts a nested proof.

The value is nil if there is no current proof. Otherwise it is a
cons cell. Its car is the name of the proof. Its cdr is the start
position of the span that contains the command that started this
proof.

To support proper undo operation, this variable should only be
changed via `proof-tree-start-proof' or `proof-tree-end-proof'.")

(defvar proof-tree-current-proof-history nil
  "Alist mapping state numbers to old values of `proof-tree-current-proof'.
Needed for undo.")

(defvar proof-tree-sequent-hash (make-hash-table :test 'equal)
  "Hash table to remember sequent ID's.
Needed because some proof assistants do not distinguish between
new subgoals, which have been created by the last proof command,
and older, currently unfocussed subgoals. If Proof General meets
a goal, it is treated as new subgoal if it is not in this hash yet.

The hash is mostly used as a set of sequent ID's. However, for
undo operations it is necessary to delete all those sequents from
the hash that have been created in a state later than the undo
state. For this purpose this hash maps sequent ID's to the state
number in which the sequent has been created.")

(defvar proof-tree-existentials-alist nil
  "Alist mapping existential variables to sequent ID's.
Used to remember which goals need a refresh when an existential
variable gets instantiated. To support undo commands the old
contents of this list must be stored in
`proof-tree-existentials-alist-history'. To ensure undo is
properly working, this variable should only be changed by using
`proof-tree-delete-existential-assoc',
`proof-tree-add-existential-assoc' or
`proof-tree-reset-existentials'.")

(defvar proof-tree-existentials-alist-history nil
  "Alist mapping state numbers to old values of `proof-tree-existentials-alist'.
Needed for undo.")
  
(defvar proof-tree-redo-display-position nil
  "Internal variable for starting the proof-tree display inside a proof.
When the proof-tree display is started in the middle of a proof
then this variable remembers the locked region. To display the
proof, everything is retracted to the beginning of the proof.
Then, the proof-tree display is switched on and
`proof-tree-handle-delayed-output-internal' sees that this
variable is non-nil and re-assert all the material that was
locked before.

If non-nil, the variable holds a list with three elements, the
current scripting buffer, the end of the locked region, and the
position of point, in this order.")

;;
;; Utilities
;;

(defun proof-tree-warning (message level)
  "Display warning MESSAGE and throw 'proof-tree-exit if LEVEL is :error."
  (display-warning '(proof-general proof-tree) message level)
  (if (or (eq level :error) (eq level :emergency))
      (throw 'proof-tree-exit nil)))

;;
;; Process creation
;;

(defun proof-tree-start-process ()
  "Start the external prooftree process.
Does also initialize the communication channel and some internal
variables."
  (let ((old-proof-tree (get-process proof-tree-process-name)))
    ;; first clean up any old processes
    (when old-proof-tree
      (delete-process old-proof-tree)
      (with-current-buffer
	  (get-buffer-create proof-tree-process-buffer)
	(insert "\n\nProcess terminated by Proof General\n\n")))
    ;; now start the new process
    (with-current-buffer
	(get-buffer-create proof-tree-process-buffer)
      (insert "Start new prooftree process\n\n"))
    (setq proof-tree-process
	  (apply 'start-process
	   proof-tree-process-name
	   proof-tree-process-buffer
	   proof-tree-program
	   proof-tree-arguments))
    (set-process-coding-system proof-tree-process 'utf-8-unix 'utf-8-unix)
    (set-process-query-on-exit-flag proof-tree-process nil)
    ;; other initializations
    (setq proof-tree-sequent-hash (make-hash-table :test 'equal)
	  proof-tree-last-state 0
	  proof-tree-existentials-alist nil
	  proof-tree-existentials-alist-history nil)))


(defun proof-tree-is-running ()
  "Return t if prooftree is properly running."
  (and proof-tree-process
       (eq (process-status proof-tree-process) 'run)))

(defun proof-tree-ensure-running ()
  "Ensure the prooftree process is running properly."
  (unless (proof-tree-is-running)
    (proof-tree-start-process)))


;;
;; Low-level communication primitives
;;

(defun proof-tree-send-goal-state (state proof-name command-string
				   current-sequent-id current-sequent-text
				   additional-sequent-ids)
  "Send the current goal state to prooftree."
  (let ((add-id-string (mapconcat 'identity additional-sequent-ids " ")))
    (process-send-string
     proof-tree-process
     (format
      (concat "current-goals state %d current-sequent %s proof-name-bytes %d "
	      "command-bytes %d sequent-text-bytes %d additional-id-bytes %d\n"
	      "%s\n%s\n%s\n%s\n")
      state current-sequent-id
      (+ (string-bytes proof-name) 1)
      (+ (string-bytes command-string) 1)
      (+ (string-bytes current-sequent-text) 1)
      (+ (string-bytes add-id-string) 1)
      proof-name
      command-string
      current-sequent-text
      add-id-string))))

(defun proof-tree-send-update-sequent (state proof-name sequent-id sequent-text)
  "Send the updated sequent text to prooftree."
  (process-send-string
   proof-tree-process
   (format
    (concat "update-sequent state %d sequent %s proof-name-bytes %d "
	    "sequent-text-bytes %d\n%s\n%s\n")
    state sequent-id
    (+ (string-bytes proof-name) 1)
    (+ (string-bytes sequent-text) 1)
    proof-name
    sequent-text)))

(defun proof-tree-send-switch-goal (proof-state proof-name current-id)
  "Send switch-to command to prooftree."
  (process-send-string
   proof-tree-process
   (format "switch-goal state %d sequent %s proof-name-bytes %d\n%s\n"
	   proof-state
	   current-id
	   (+ (string-bytes proof-name) 1)
	   proof-name)))

(defun proof-tree-send-proof-completed (state proof-name cmd-string)
  "Send proof completed to prooftree."
  (process-send-string
   proof-tree-process
   (format
    "proof-complete state %d proof-name-bytes %d command-bytes %d\n%s\n%s\n"
    state
    (+ (string-bytes proof-name) 1)
    (+ (string-bytes cmd-string) 1)
    proof-name
    cmd-string)))

(defun proof-tree-send-undo (proof-state)
  "Tell prooftree to undo."
  (process-send-string proof-tree-process
		       (format "undo-to state %d\n" proof-state)))

(defun proof-tree-send-quit-proof (proof-name)
  "Tell prooftree to close the window for PROOF-NAME."
  (process-send-string proof-tree-process
		       (format "quit-proof proof-name-bytes %d\n%s\n"
			       (+ (string-bytes proof-name) 1)
			       proof-name)))

;;
;; proof-tree-existentials-alist manipulations and history
;;

(defun proof-tree-record-existentials-state (state &optional dont-copy)
  "Store the current state of `proof-tree-existentials-alist' for undo.
Usually this involves making a copy of
`proof-tree-existentials-alist' because of the destructive
updates used on that list. If optional argument DONT-COPY is
non-nil no copy is done."
  (setq proof-tree-existentials-alist-history
	(cons (cons state
		    (if dont-copy
			 proof-tree-existentials-alist
		      (copy-alist proof-tree-existentials-alist)))
	      proof-tree-existentials-alist-history)))

(defun proof-tree-undo-state-var (proof-state var-symbol history-symbol)
  "Undo changes to VAR-SYMBOL using HISTORY-SYMBOL.
This is a general undo function for variables that keep their
undo information in a alist that maps state numbers to old
values. Argument PROOF-STATE is the state to reestablish,
VAR-SYMBOL is (the symbol of) the variable to undo and
HISTORY-SYMBOL is (the symbol of) the undo history alist."
  (let ((undo-not-finished t)
	(history (symbol-value history-symbol))
	(var (symbol-value var-symbol)))
    (while (and undo-not-finished history)
      (if (>= (caar history) proof-state)
	  (progn
	    (setq var (cdr (car history)))
	    (setq history (cdr history)))
	(setq undo-not-finished nil)))
    (set var-symbol var)
    (set history-symbol history)))

(defun proof-tree-undo-existentials (proof-state)
  "Undo changes in `proof-tree-existentials-alist'.
Change `proof-tree-existentials-alist' back to its contents in
state PROOF-STATE."
  (proof-tree-undo-state-var proof-state
			     'proof-tree-existentials-alist
			     'proof-tree-existentials-alist-history))

(defun proof-tree-delete-existential-assoc (state ex-assoc)
  "Delete mapping EX-ASSOC from 'proof-tree-existentials-alist'."
  (proof-tree-record-existentials-state state)
  (setq proof-tree-existentials-alist
	(delq ex-assoc proof-tree-existentials-alist)))
  
(defun proof-tree-add-existential-assoc (state ex-var sequent-id)
  "Add the mapping EX-VAR -> SEQUENT-ID to 'proof-tree-existentials-alist'.
Do nothing if this mapping does already exist."
  (let ((ex-var-assoc (assoc ex-var proof-tree-existentials-alist)))
    (if ex-var-assoc
	(unless (member sequent-id (cdr ex-var-assoc))
	  (proof-tree-record-existentials-state state)
	  (setcdr ex-var-assoc (cons sequent-id (cdr ex-var-assoc))))
      (proof-tree-record-existentials-state state)
      (setq proof-tree-existentials-alist
	    (cons (cons ex-var (list sequent-id))
		  proof-tree-existentials-alist)))))

(defun proof-tree-reset-existentials (proof-state)
  "Clear the mapping in `proof-tree-existentials-alist'."
  (proof-tree-record-existentials-state proof-state 'dont-copy)
  (setq proof-tree-existentials-alist nil))


;;
;; proof-tree-current-proof manipulations and history
;;

(defun proof-tree-record-current-proof-state (state)
  "Store current state of `proof-tree-current-proof' for undo purposes."
  (setq proof-tree-current-proof-history
	(cons (cons state proof-tree-current-proof)
	      proof-tree-current-proof-history)))

(defun proof-tree-undo-current-proof (proof-state)
  "Reestablish state PROOF-STATE of `proof-tree-current-proof'."
  (proof-tree-undo-state-var proof-state
			     'proof-tree-current-proof
			     'proof-tree-current-proof-history))

(defun proof-tree-start-proof (state name start-pos)
  "Set `proof-tree-current-proof'."
  (proof-tree-record-current-proof-state state)
  (setq proof-tree-current-proof (cons name start-pos)))

(defun proof-tree-end-proof (state)
  "Clear `proof-tree-current-proof'."
  (proof-tree-record-current-proof-state state)
  (setq proof-tree-current-proof nil))


;;
;; Process output from the proof assistant
;;

(defun proof-tree-show-goal-callback ()
  "Callback for display-goal commands inserted by this package."
  ())

(defun proof-tree-urgent-action (cmd flags)
  "Handle urgent points before the next item is sent to the proof assistant.
Schedule goal updates when existential variables have changed and
call `proof-tree-urgent-action-hook'. All this is only done if
the current output does not come from a command (with the
'proof-tree-show-subgoal flag) that this package inserted itself.

The not yet delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "PTUA flags %s start %s end %s pal %s ptea %s"
  ;; 	   flags
  ;; 	   proof-shell-delayed-output-start
  ;; 	   proof-shell-delayed-output-end
  ;; 	   proof-action-list
  ;; 	   proof-tree-existentials-alist)
  (let* ((proof-info (funcall proof-tree-get-proof-info cmd flags))
	 (start proof-shell-delayed-output-start)
	 (end proof-shell-delayed-output-end)
	 inst-ex-vars)
    (when (and (not (memq 'proof-tree-show-subgoal flags))
	       (> (car proof-info) proof-tree-last-state))
      ;; Only deal with existentials if the proof assistant has them
      ;; (i.e., proof-tree-existential-regexp is set) and if there are some
      ;; goals with existentials.
      (when (and proof-tree-existential-regexp
		 proof-tree-existentials-alist)
	(setq inst-ex-vars
	      (with-current-buffer proof-shell-buffer
		(funcall proof-tree-extract-instantiated-existentials
			 start end)))
	(dolist (ex-var inst-ex-vars)
	  (let ((var-goal-assoc (assoc ex-var proof-tree-existentials-alist)))
	    (when var-goal-assoc
	      (dolist (sequent-id (cdr var-goal-assoc))
		(let ((show-cmd
		       (funcall proof-tree-show-sequent-command sequent-id)))
		  (if show-cmd
		      (setq proof-action-list
			    (cons (proof-shell-action-list-item
				   show-cmd
				   'proof-tree-show-goal-callback
				   '(no-response-display
				     no-goals-display
				     proof-tree-show-subgoal))
				  proof-action-list)))))
	      (proof-tree-delete-existential-assoc (car proof-info)
						   var-goal-assoc)))))
      (run-hooks 'proof-tree-urgent-action-hook))
    ;; (message "PTUA END pal %s ptea %s"
    ;; 	   proof-action-list
    ;; 	   proof-tree-existentials-alist)
  ))


;;
;; Process output from the proof assistant
;;

(defun proof-tree-register-existentials (current-state sequent-id sequent-text)
  "Register existential variables in SEQUENT-TEXT.
If SEQUENT-TEXT contains existential variables, then SEQUENT-ID
is stored in `proof-tree-existentials-alist'."
  (if proof-tree-existential-regexp
      (let ((start 0))
	(while (proof-string-match proof-tree-existential-regexp
				   sequent-text start)
	  (setq start (match-end 0))
	  (proof-tree-add-existential-assoc current-state
					    (match-string 1 sequent-text)
					    sequent-id)))))

(defun proof-tree-extract-goals (start end)
  "Extract the current goal state information from the delayed output.
If there is a current goal, return a list containing with (in
this order) the ID of the current sequent, the text of the
current sequent and the list of ID's of additionally open goals.
The delayed output is expected between START and END in the
current buffer."
  (goto-char start)
  (if (proof-re-search-forward proof-tree-current-goal-regexp end t)
      (let ((sequent-id (buffer-substring-no-properties (match-beginning 1)
							(match-end 1)))
	    (sequent-text
	     (buffer-substring-no-properties
	      (match-beginning 2) (match-end 2)))
	    additional-goal-ids)
	(goto-char start)
	(while (proof-re-search-forward proof-tree-additional-subgoal-ID-regexp
					end t)
	  (let ((next-start (match-end 0))
		(other-id (buffer-substring-no-properties (match-beginning 1)
							  (match-end 1))))
	    (setq additional-goal-ids (cons other-id additional-goal-ids))
	    (goto-char next-start)))
	(setq additional-goal-ids (nreverse additional-goal-ids))
	(list sequent-id sequent-text additional-goal-ids))
    nil))

(defun proof-tree-handle-proof-progress (cmd-string proof-info)
  "Send CMD-STRING and goals in delayed output to prooftree.
This function is called if there is some real progress in a
proof. This function sends the current state, the current goal
and the list of additional open subgoals to prooftree. Prooftree
will sort out the rest.

The delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "PTHPO cmd |%s| info %s flags %s start %s end %s"
  ;; 	   cmd proof-info flags
  ;; 	   proof-shell-delayed-output-start
  ;; 	   proof-shell-delayed-output-end)
  (let* ((start proof-shell-delayed-output-start)
	 (end   proof-shell-delayed-output-end)
	 (proof-state (car proof-info))
	 (proof-name (cadr proof-info))
	 (current-goals (proof-tree-extract-goals start end)))
    (if current-goals
	(let ((current-sequent-id (car current-goals))
	      (current-sequent-text (nth 1 current-goals))
	      ;; nth 2 current-goals  contains the  additional ID's
	      )
	  ;; send all to prooftree
	  (proof-tree-send-goal-state
	   proof-state proof-name cmd-string
	   current-sequent-id
	   current-sequent-text
	   (nth 2 current-goals))
	  ;; put current sequent into hash (if it is not there yet)
	  (unless (gethash current-sequent-id proof-tree-sequent-hash)
	    (puthash current-sequent-id proof-state proof-tree-sequent-hash))
	  (proof-tree-register-existentials proof-state
					    current-sequent-id
					    current-sequent-text))
      
      ;; no current goal found, maybe the proof has been completed?
      (goto-char start)
      (if (proof-re-search-forward proof-tree-proof-completed-regexp end t)
	  (progn
	    (proof-tree-send-proof-completed proof-state proof-name cmd-string)
	    (proof-tree-reset-existentials proof-state))))))

(defun proof-tree-handle-navigation (proof-info)
  "Handle a navigation command.
This function is called if there was a navigation command, which
results in a different goal being current now.

The delayed output of the navigation command is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  (let ((start proof-shell-delayed-output-start)
	(end   proof-shell-delayed-output-end)
	(proof-state (car proof-info))
	(proof-name (cadr proof-info)))
    (goto-char start)
    (if (proof-re-search-forward proof-tree-current-goal-regexp end t)
	(let ((current-id (buffer-substring-no-properties (match-beginning 1)
							  (match-end 1))))
	  ;; send all to prooftree
	  (proof-tree-send-switch-goal proof-state proof-name current-id)))))


(defun proof-tree-handle-proof-command (cmd proof-info)
  "Display current goal in prooftree unless CMD should be ignored."
  ;; (message "PTHPC")
  (let ((proof-state (car proof-info))
	(cmd-string (mapconcat 'identity cmd " ")))
    (unless (proof-string-match proof-tree-ignored-commands-regexp cmd-string)
      (if (proof-string-match proof-tree-navigation-command-regexp cmd-string)
	  (proof-tree-handle-navigation proof-info)
	(proof-tree-handle-proof-progress cmd-string proof-info)))
    (setq proof-tree-last-state (car proof-info))))
    
(defun proof-tree-handle-undo (proof-info)
  "Undo prooftree to current state.
Send the undo command to prooftree and undo changes to the
internal state of this package. The latter involves currently two
points:
* delete those goals from `proof-tree-sequent-hash' that have
  been generated after the state to which we undo now
* change proof-tree-existentials-alist and
  proof-tree-current-proof back to its previous contents"
  ;; (message "PTHU info %s" proof-info)
  (let ((proof-state (car proof-info)))
    ;; delete sequents from the hash
    (maphash
     (lambda (sequent-id state)
       (if (>= state proof-state)
	   (remhash sequent-id proof-tree-sequent-hash)))
     proof-tree-sequent-hash)
    ;; undo changes in other state vars
    (proof-tree-undo-existentials proof-state)
    (proof-tree-undo-current-proof proof-state)
    ;; send undo
    (if (proof-tree-is-running)
	(proof-tree-send-undo proof-state))
    (setq proof-tree-last-state (- proof-state 1))))


(defun proof-tree-update-sequent (proof-info)
  "Prepare an update-sequent command for prooftree.
This function processes delayed output that the proof assistant
generated in response to commands that Proof General inserted in
order to keep prooftree up-to-date. Such commands are tagged with
a 'proof-tree-show-subgoal flag.

This function uses `proof-tree-update-goal-regexp' to find a
sequent and its ID in the delayed output. If something is found
an appropriate update-sequent command is sent to prooftree.

The delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  (let ((start proof-shell-delayed-output-start)
	(end   proof-shell-delayed-output-end)
	(proof-state (car proof-info))
	(proof-name (cadr proof-info)))
    (goto-char start)
    (if (proof-re-search-forward proof-tree-update-goal-regexp end t)
	(let ((sequent-id (buffer-substring-no-properties (match-beginning 1)
							  (match-end 1)))
	      (sequent-text
	       (buffer-substring-no-properties
		(match-beginning 2) (match-end 2))))
	  (proof-tree-send-update-sequent
	   proof-state proof-name sequent-id sequent-text)
	  ;; put current sequent into hash (if it is not there yet)
	  (unless (gethash sequent-id proof-tree-sequent-hash)
	    (puthash sequent-id proof-state proof-tree-sequent-hash))
	  (proof-tree-register-existentials proof-state sequent-id sequent-text)
	  ;; remember state for undo
	  (setq proof-tree-last-state proof-state)))))


(defun proof-tree-handle-delayed-output-internal (cmd flags span)
  "Process delayed output for prooftree.
Examines the delayed output in order to find out whether some
undo command occured, whether there is a new current goal, or
whether there is output that has been generated for prooftree
only. Then the appropriate action is taken, which eventually will
send appropriate commands to prooftree.

This function is also responsible for maintaining
`proof-tree-current-proof' consistent.

This function is called from `proof-shell-filter-manage-output',
after `proof-shell-exec-loop' has finished. It can therefore call
`proof-assert-until-point'. This function is therefore
responsible for reasserting material when the user started the
proof-tree display in the middle of a proof. For that it examines
`proof-tree-redo-display-position' and takes appropriate actions
if `proof-action-list' is empty.

All arguments are (former) fields of the `proof-action-list'
entry that is now finally retired. CMD is the command, FLAGS are
the flags and SPAN is the span."
  ;; (message "PTHDOI cmd %s flags %s" cmd flags)
  (unless (memq 'invisible flags)
    (let* ((proof-info (funcall proof-tree-get-proof-info cmd flags))
	   (current-proof-name (cadr proof-info)))
      (save-excursion
	(if (<= (car proof-info) proof-tree-last-state)
	    ;; went back to some old state: there must have been an undo command
	    (proof-tree-handle-undo proof-info)

	  ;; else -- no undo command
	  ;; first maintain proof-tree-current-proof
	  (cond
	   ((and (null proof-tree-current-proof) current-proof-name)
	    ;; started a new proof
	    (proof-tree-start-proof (car proof-info) current-proof-name
				    (span-start span)))
	   ((and proof-tree-current-proof (null current-proof-name))
	    ;; finished the current proof
	    (proof-tree-end-proof (car proof-info))
	    (setq proof-tree-external-display nil))
	   ((and proof-tree-current-proof current-proof-name
		 (not (equal (car proof-tree-current-proof)
			     current-proof-name)))
	    ;; new proof before old was finished?
	    (proof-tree-warning
	     "Nested proofs are not supported in prooftree display"
	     :warning)
	    ;; try to keep consistency nevertheless
	    (proof-tree-start-proof (car proof-info) current-proof-name
				    (span-start span))))

	  ;; send stuff to prooftree now
	  (cond
	   ((and proof-tree-external-display
		 (memq 'proof-tree-show-subgoal flags))
	    ;; display of a known sequent to update it in prooftree
	    (proof-tree-ensure-running)
	    (proof-tree-update-sequent proof-info))
	   ((and proof-tree-external-display current-proof-name)
	    ;; we are inside a proof: display something
	    (proof-tree-ensure-running)
	    (proof-tree-handle-proof-command cmd proof-info)))))

      ;; finally check if must reassert some part of the proof, because
      ;; someone started the proof-tree display in the middle of a proof.
      (when (and proof-tree-redo-display-position (null proof-action-list))
	;; bind proof-tree-redo-display-position locally to reset it before any
	;; error can occur
	(let ((redo-pos proof-tree-redo-display-position))
	  (setq proof-tree-redo-display-position nil)
	  (setq proof-tree-external-display t)
	  (with-current-buffer (car redo-pos)
	    (goto-char (nth 1 redo-pos))
	    (proof-assert-until-point)
	    (goto-char (nth 2 redo-pos))))))))


(defun proof-tree-handle-delayed-output (cmd flags span)
  "Process delayed output for prooftree.
This function is the main entry point of the Proof General
prooftree support. It examines the delayed output in order to
take appropriate actions and maintains some part of the internal
state.

Actually all useful work is done inside
`proof-tree-handle-delayed-output-internal', see there for more
details. This function is only a wrapper around
`proof-tree-handle-delayed-output-internal' to catch non-local
exits (which are not present in the current version any more).

The arguments are (former) fields of the `proof-action-list'
entry that is now finally retired. CMD is the command, FLAGS are
the flags and SPAN is the span."
  (catch 'proof-tree-exit
    (proof-tree-handle-delayed-output-internal cmd flags span)))

;;
;; User interface
;;

(defun proof-tree-display-current-proof ()
  "Start an external proof-tree display for the current proof.
Coq (and probably other proof assistants as well) does not
support outputing the current proof tree. Therefore this function
retracts to the start of the current proof, switches the
proof-tree display on, and reasserts then until the former end of
the locked region."
  (unless (and proof-script-buffer
	       (equal proof-script-buffer (current-buffer)))
    (error
     "Enabling prooftree inside a proof outside the current scripting buffer"))
  ;; XXX only continue if the proofer is idle, howto check this?
  (assert proof-locked-span)
  (message "Start proof-tree display for current proof")
  (let ((point (point))
	(locked-end (span-end proof-locked-span)))
    (setq proof-tree-redo-display-position
	  (list (current-buffer) locked-end point))
    (goto-char (cdr proof-tree-current-proof))
    (proof-retract-until-point)))

(defun proof-tree-external-display-toggle ()
  "Toggle the external proof-tree display.
When called outside a proof the external proof-tree display will
be enabled for the next proof. When called inside a proof the
proof display will be created for the current proof. If the
external proof-tree display is currently on, then this toggle
will switch it off. At the end of the proof the proof-tree
display is switched off."
  (interactive)
  (cond
   (proof-tree-external-display
    ;; Currently on -> switch off
    (setq proof-tree-external-display nil)
    (if proof-tree-current-proof
	(proof-tree-send-quit-proof (car proof-tree-current-proof)))
    (message "External proof-tree display switched off"))
   (proof-tree-current-proof
    ;; Currently off and inside a proof -> start for this proof
    (proof-tree-display-current-proof))
   (t
    ;; Currently off and outside a proof -> switch on for the next proof
    (setq proof-tree-external-display t)
    (message "External proof-tree display switched on for the next proof"))))
    

;;
;; Trailer
;; 

(provide 'proof-tree)

;;; tree-tree.el ends here
