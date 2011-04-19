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
;; probably other proof assistants as well) do not provide any
;; information about which subgoals are new and have been created by
;; the last proof command and which subgoals stem from older proof
;; commands.
;;
;; To solve this problem prooftree relies on unique identification
;; strings of goals, which are called goal or sequent ID's in the
;; code. With these ID's it is easy to keep track which goals are new.
;;
;; A second problem is that for an undo command Coq (and probably
;; other proof assistants as well) do not tell which subgoals and
;; which finished branches must be deleted. Therefore prooftree needs
;; a continuously increasing proof state number and keeps a complete
;; undo history for every proof.
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
;; Some aspects can however not be delayed. Those are treated by the
;; hook `proof-tree-urgent-action-hook'. Its primary use is for
;; inserting special goal-displaying commands into `proof-action-list'
;; before the next real proof command runs.
;;

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
  "Regexp to match the a goal and its ID.
The regexp is matched against the output of additional show-goal
commands inserted by Proof General. Proof General inserts such
commands to update the goal text in prooftree. This is necessary,
for instance, when existential variables get instanciated."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-additional-subgoal-ID-regexp nil
  "Regular expression to match ID's of additional subgoals.
This regexp is used to extract the ID's of all additionally open
goals. The regexp is used in a while loop and must match one
subgoal ID with subgroup 1."
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
contains in the following order * the current state number (as
positive integer) * the name of the current proof (as string)

The state number is used to implement undo in prooftree. The
proof name is used to distinguish different proofs inside prooftree."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-urgent-action-hook ()
  "Normal hook for prooftree actions that cannot be delayed.
This hook is called from inside `proof-shell-exec-loop' after the
preceeding command has been choped off `proof-action-list' and
before the next command is sent to the proof assistant. This hook
can therefore be used to insert additional commands into
`proof-action-list' that must be executed before the next real
proof command.

This hook is used, for instance, for Coq to insert Show commands
for newly generated subgoals. (The normal Coq output does not
contain the complete sequent text of newly generated subgoals.)"
  :type 'hook
  :group 'proof-tree-internals)


;;
;; Internal variables
;;

(defvar proof-tree-process nil
  "Emacs lisp process object of the prooftree process.")

(defconst proof-tree-process-name "proof-tree"
  "Name of the prooftree process for Emacs lisp.")

(defconst proof-tree-process-buffer
  (concat "*" proof-tree-process-name "*")
  "Buffer for stdout and stderr of the prooftree process.")

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

(defvar proof-tree-last-state 0
  "Last state of the proof assistant.
Used for undoing in prooftree.")


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
    (setq proof-tree-sequent-hash (make-hash-table :test 'equal))
    (setq proof-tree-last-state 0)))


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

(defun proof-tree-send-goal-state (state proof-name command
				   current-sequent-id current-sequent-text
				   additional-sequent-ids)
  "Send the current goal state to prooftree."
  (let ((cmd-string (mapconcat 'identity command " "))
	(add-id-string (mapconcat 'identity additional-sequent-ids " ")))
    (process-send-string
     proof-tree-process
     (format
      (concat "current-goals state %d current-sequent %s proof-name-bytes %d "
	      "command-bytes %d sequent-text-bytes %d additional-id-bytes %d\n"
	      "%s\n%s\n%s\n%s\n")
      state current-sequent-id
      (+ (string-bytes proof-name) 1)
      (+ (string-bytes cmd-string) 1)
      (+ (string-bytes current-sequent-text) 1)
      (+ (string-bytes add-id-string) 1)
      proof-name
      cmd-string
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

(defun proof-tree-send-proof-completed (state proof-name cmd)
  "Send proof completed to prooftree."
  (let ((cmd-string (mapconcat 'identity cmd " ")))
    (process-send-string
     proof-tree-process
     (format
      "proof-complete state %d proof-name-bytes %d command-bytes %d\n%s\n%s\n"
      state
      (+ (string-bytes proof-name) 1)
      (+ (string-bytes cmd-string) 1)
      proof-name
      cmd-string))))  


(defun proof-tree-send-undo (proof-state)
  "Tell prooftree to undo."
  (process-send-string proof-tree-process
		       (format "undo-to state %d\n" proof-state)))


;;
;; Process output from the proof assistant
;;

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

  

(defun proof-tree-handle-proof-output (cmd proof-info)
  "Send CMD and goals in delayed output to prooftree.
This function is called indirectly from
`proof-shell-filter-manage-output' if there is some progress in a
proof and if `proof-tree-external-display' is non-nil. This
function sends the current state, the current goal and the list
of additional open subgoals to prooftree.

The delayed output is in the region
\[proof-shell-last-output-start, proof-shell-last-output-end]."
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
	      ;; nth 1 current-goals  contains the  sequent text
	      ;; nth 2 current-goals  contains the  additional ID's
	      )
	  ;; send all to prooftree
	  (proof-tree-send-goal-state
	   proof-state proof-name cmd
	   current-sequent-id
	   (nth 1 current-goals)
	   (nth 2 current-goals))
	  ;; put current sequent into hash (if it is not there yet)
	  (unless (gethash current-sequent-id proof-tree-sequent-hash)
	    (puthash current-sequent-id proof-state proof-tree-sequent-hash))
	  ;; remember state for undo
	  (setq proof-tree-last-state proof-state))
      ;; no current goal found, maybe the proof has been completed?
      (goto-char start)
      (if (proof-re-search-forward proof-tree-proof-completed-regexp end t)
	  (progn
	    (proof-tree-send-proof-completed proof-state proof-name cmd)
	    (setq proof-tree-last-state proof-state))))))

    
(defun proof-tree-handle-undo (proof-info)
  "Undo prooftree to current state.
Send the undo command to prooftree and delete those goals from
`proof-tree-sequent-hash' that have been generated after the
state to which we undo now."
  (let ((proof-state (car proof-info)))
    ;; delete sequents from the hash
    (maphash
     (lambda (sequent-id state)
       (if (>= state proof-state)
	   (remhash sequent-id proof-tree-sequent-hash)))
     proof-tree-sequent-hash)
    ;; send undo
    (proof-tree-send-undo proof-state)
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
\[proof-shell-last-output-start, proof-shell-last-output-end]."
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
	  ;; remember state for undo
	  (setq proof-tree-last-state proof-state)))))


(defun proof-tree-handle-delayed-output (cmd flags)
  "Process delayed output for prooftree.
This function is the main entry point of the Proof General
prooftree support. It examines the delayed output in order to
find out whether an some undo command occured, there is a new
current goal, or whether there is output that has been generated
for prooftree only. Then the appropriate action is taken, which
eventually will send appropriate commands to prooftree."
  (unless (memq 'invisible flags)
    (let ((proof-info (funcall proof-tree-get-proof-info cmd flags)))
      (save-excursion
	(cond
	 ((<= (car proof-info) proof-tree-last-state)
	  ;; went back to some old state: there must have been an undo command
	  (if (proof-tree-is-running)
	      (proof-tree-handle-undo proof-info)))
	 ((and proof-tree-external-display
	       (memq 'proof-tree-show-subgoal flags))
	  ;; display of a known sequent to update it in prooftree
	  (proof-tree-ensure-running)
	  (proof-tree-update-sequent proof-info))
	 ((and proof-tree-external-display
	       (car (cdr proof-info)))
	  ;; we are inside a proof: display something
	  (proof-tree-ensure-running)
	  (proof-tree-handle-proof-output cmd proof-info)))))))


;;
;; Trailer
;; 

(provide 'proof-tree)

;;; tree-tree.el ends here
