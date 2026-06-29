; zdd-waterfall-plan-search.lisp
;
; An untrusted program-mode driver for trying finite candidate proof plans with
; ACL2's own prover.  A successful search emits an ordinary DEFTHM event with
; the selected hints.  Hence search bugs can waste time or choose poor hints,
; but cannot admit a false theorem.

(in-package "ACL2")

(include-book "zdc-adp-proof-plan-optimizer")
(include-book "tools/prove-dollar" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zdd-waterfall-plan-search
  :parents (zdc-adp-proof-plan-optimizer)
  :short "Finite untrusted plan search followed by ordinary waterfall replay."
  :long
  "<p>A search candidate is <tt>(name logical-plan hints)</tt>.  The logical
  plan supplies the finite action/cost/provenance object from the preceding
  books.  The hints are ordinary ACL2 hints.  The program-mode driver calls
  <tt>PROVE$</tt> under a step limit, records failures and prover-step counts,
  and stops at the first successful candidate.</p>

  <p>The macro <tt>WPS-DEFTHM</tt> stores the search receipt in a table and then
  emits a normal <tt>DEFTHM</tt> using the winning hints.  The search result has
  no trusted logical status.  If the hints do not really prove the formula,
  the emitted theorem event fails in the ordinary way.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Candidate and receipt syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wps-candidate-name (candidate)
  (symbol-fix (car candidate)))

(defun wps-candidate-plan (candidate)
  (cadr candidate))

(defun wps-candidate-hints (candidate)
  (caddr candidate))

(defun wps-candidatep (candidate)
  (and (true-listp candidate)
       (equal (len candidate) 3)
       (symbolp (car candidate))
       (pp-plan-validp (cadr candidate))
       (true-listp (caddr candidate))))

(defun wps-search-receipt (name plan hints steps failures)
  (list :waterfall-search-receipt
        (symbol-fix name)
        plan
        hints
        (ifix steps)
        failures))

(defun wps-receipt-selected-name (receipt)
  (symbol-fix (cadr receipt)))

(defun wps-receipt-plan (receipt)
  (caddr receipt))

(defun wps-receipt-hints (receipt)
  (cadddr receipt))

(defun wps-receipt-steps (receipt)
  (ifix (car (cddddr receipt))))

(defun wps-receipt-failures (receipt)
  (cadr (cddddr receipt)))

(defun wps-search-receiptp (receipt)
  (and (true-listp receipt)
       (equal (len receipt) 6)
       (eq (car receipt) :waterfall-search-receipt)
       (symbolp (cadr receipt))
       (pp-plan-validp (caddr receipt))
       (true-listp (cadddr receipt))
       (integerp (car (cddddr receipt)))
       (true-listp (cadr (cddddr receipt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Program-mode proof search
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wps-last-steps (state)
  (declare (xargs :mode :program :stobjs state))
  (let ((steps (last-prover-steps state)))
    (if (integerp steps) steps 0)))

(defun wps-try-candidates-aux
  (term candidates step-limit failures state)
  (declare (xargs :mode :program :stobjs state))
  (cond
   ((endp candidates)
    (value nil))
   ((not (wps-candidatep (car candidates)))
    (wps-try-candidates-aux
     term (cdr candidates) step-limit
     (cons (list (wps-candidate-name (car candidates))
                 :invalid-candidate 0)
           failures)
     state))
   (t
    (let* ((candidate (car candidates))
           (name (wps-candidate-name candidate))
           (plan (wps-candidate-plan candidate))
           (hints (wps-candidate-hints candidate)))
      (mv-let
       (erp provedp state)
       (prove$ term
               :hints hints
               :step-limit step-limit
               :skip-proofs nil
               :with-output (:off :all :on error :gag-mode nil))
       (let ((steps (wps-last-steps state)))
         (cond
          ((and (not erp) provedp)
           (value
            (wps-search-receipt
             name plan hints steps (reverse failures))))
          (t
           (wps-try-candidates-aux
            term (cdr candidates) step-limit
            (cons (list name
                        (if erp :translation-error :proof-failure)
                        steps)
                  failures)
            state)))))))))

(defun wps-try-candidates (term candidates step-limit state)
  (declare (xargs :mode :program :stobjs state))
  (wps-try-candidates-aux term candidates step-limit nil state))

(defun wps-search-and-emit-fn
  (name term candidates step-limit state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let
   (erp receipt state)
   (wps-try-candidates term candidates step-limit state)
   (cond
    (erp (mv erp nil state))
    ((null receipt)
     (er soft 'wps-defthm
         "No candidate proof plan proved theorem ~x0 under step limit ~x1."
         name step-limit))
    (t
     (let ((hints (wps-receipt-hints receipt)))
       (value
        `(progn
           (table wps-proof-receipts ',name ',receipt)
           (defthm ,name ,term :hints ,hints))))))))

(defmacro wps-defthm (name term candidates &key (step-limit '100000))
  `(make-event
    (wps-search-and-emit-fn
     ',name ',term ',candidates ,step-limit state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Live search-and-replay pressure test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wps-fold (xs)
  (if (endp xs)
      0
    (1+ (wps-fold (cdr xs)))))

(defthm wps-fold-is-len
  (equal (wps-fold xs) (len xs))
  :hints (("Goal"
           :induct (wps-fold xs)
           :in-theory (enable wps-fold len))))

(deftheory wps-fold-semantic-interface
  '(wps-fold-is-len len-of-append))

(wps-defthm
 wps-fold-of-append
 (equal (wps-fold (append x y))
        (+ (wps-fold x) (wps-fold y)))
 ((empty-plan
   ((:theory empty-theory
             nil (empty-theory-tried)
             (1 0 5 0 1)))
   (("Goal" :in-theory nil)))
  (fold-induction-plan
   ((:theory fold-and-append
             nil (definitions-open)
             (0 1 80 2 0))
    (:induct fold-on-x
             (definitions-open) (goal-closed)
             (0 2 140 0 0)))
   (("Goal"
     :in-theory (theory 'wps-fold-semantic-interface)))))
 :step-limit 1000)

(assert-event
 (equal (wps-fold (append '(1 2 3) '(4 5)))
        (+ (wps-fold '(1 2 3))
           (wps-fold '(4 5)))))
