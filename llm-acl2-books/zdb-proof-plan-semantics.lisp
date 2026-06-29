; zdb-proof-plan-semantics.lisp
;
; A finite logical language for waterfall proof plans.  The language does not
; prove ACL2 goals.  It describes admissible proof actions, their feature
; preconditions/effects, and a five-coordinate cost.  Later program-mode books
; may try such plans, but an ordinary DEFTHM remains the final checker.

(in-package "ACL2")

(include-book "zda-waterfall-theory-capsules")
(include-book "xdoc/top" :dir :system)

(defxdoc zdb-proof-plan-semantics
  :parents (zda-waterfall-theory-capsules)
  :short "Finite proof actions, feature flow, cost vectors, and receipts."
  :long
  "<p>A proof action is
  <tt>(kind payload requires provides cost)</tt>.  The payload is deliberately
  uninterpreted at this logical layer.  Requirements and provisions are finite
  symbol sets.  The cost has five natural coordinates: failed-attempt risk,
  expected subgoals, waterfall steps, enabled runes, and extension fragility.
  Executable drivers may interpret payloads as theories, expansions, induction
  schemes, case splits, arithmetic modes, or verified clause processors.</p>

  <p>The semantics is intentionally modest.  It certifies feature flow, plan
  feasibility, cost accumulation, and replay receipts.  It makes no soundness
  claim about a proposed proof.  ACL2's ordinary theorem admission remains the
  only proof-producing boundary.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Five-coordinate costs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pp-nat-at (i xs)
  (nfix (nth (nfix i) xs)))

(defun pp-cost (attempt-risk subgoals steps runes fragility)
  (list (nfix attempt-risk)
        (nfix subgoals)
        (nfix steps)
        (nfix runes)
        (nfix fragility)))

(defun pp-costp (x)
  (and (true-listp x)
       (equal (len x) 5)
       (nat-listp x)))

(defun pp-cost-fix (x)
  (pp-cost (pp-nat-at 0 x)
           (pp-nat-at 1 x)
           (pp-nat-at 2 x)
           (pp-nat-at 3 x)
           (pp-nat-at 4 x)))

(defun pp-cost+ (x y)
  (pp-cost (+ (pp-nat-at 0 x) (pp-nat-at 0 y))
           (+ (pp-nat-at 1 x) (pp-nat-at 1 y))
           (+ (pp-nat-at 2 x) (pp-nat-at 2 y))
           (+ (pp-nat-at 3 x) (pp-nat-at 3 y))
           (+ (pp-nat-at 4 x) (pp-nat-at 4 y))))

(defun pp-cost-score (weights cost)
  (+ (* (pp-nat-at 0 weights) (pp-nat-at 0 cost))
     (* (pp-nat-at 1 weights) (pp-nat-at 1 cost))
     (* (pp-nat-at 2 weights) (pp-nat-at 2 cost))
     (* (pp-nat-at 3 weights) (pp-nat-at 3 cost))
     (* (pp-nat-at 4 weights) (pp-nat-at 4 cost))))

(defthm pp-costp-of-pp-cost
  (pp-costp (pp-cost a b c d e)))

(defthm pp-costp-of-pp-cost-fix
  (pp-costp (pp-cost-fix x)))

(defthm pp-costp-of-pp-cost+
  (pp-costp (pp-cost+ x y)))

(defthm natp-of-pp-cost-score
  (natp (pp-cost-score weights cost))
  :rule-classes :type-prescription)

(defthm pp-cost+-commutative
  (equal (pp-cost+ x y)
         (pp-cost+ y x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Proof actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *pp-action-kinds*
  '(:theory :expand :induct :cases :forward
    :linear :nonlinear :clause-processor))

(defun pp-action-kind (action)
  (let ((kind (car action)))
    (if (member-eq kind *pp-action-kinds*)
        kind
      :theory)))

(defun pp-action-payload (action)
  (cadr action))

(defun pp-action-requires (action)
  (wtc-symbol-set (caddr action)))

(defun pp-action-provides (action)
  (wtc-symbol-set (cadddr action)))

(defun pp-action-cost (action)
  (pp-cost-fix (car (cddddr action))))

(defun pp-action-validp (action)
  (and (true-listp action)
       (equal (len action) 5)
       (member-eq (car action) *pp-action-kinds*)
       (symbol-listp (caddr action))
       (no-duplicatesp-equal (caddr action))
       (symbol-listp (cadddr action))
       (no-duplicatesp-equal (cadddr action))
       (pp-costp (car (cddddr action)))))

(defun pp-action-enabledp (action features)
  (subsetp-equal (pp-action-requires action)
                 (wtc-symbol-set features)))

(defun pp-action-apply (action features)
  (wtc-symbol-set
   (union-equal (wtc-symbol-set features)
                (pp-action-provides action))))

(defthm symbol-listp-of-pp-action-requires
  (symbol-listp (pp-action-requires action))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (caddr action))))
           :in-theory (e/d (pp-action-requires)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm symbol-listp-of-pp-action-provides
  (symbol-listp (pp-action-provides action))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (cadddr action))))
           :in-theory (e/d (pp-action-provides)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm pp-costp-of-pp-action-cost
  (pp-costp (pp-action-cost action))
  :hints (("Goal"
           :use ((:instance pp-costp-of-pp-cost-fix
                            (x (car (cddddr action)))))
           :in-theory (e/d (pp-action-cost)
                           (pp-costp-of-pp-cost-fix)))))

(defthm symbol-listp-of-pp-action-apply
  (symbol-listp (pp-action-apply action features))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (union-equal
                                 (wtc-symbol-set features)
                                 (pp-action-provides action)))))
           :in-theory (e/d (pp-action-apply)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm no-duplicatesp-equal-of-pp-action-apply
  (no-duplicatesp-equal (pp-action-apply action features))
  :hints (("Goal"
           :use ((:instance no-duplicatesp-equal-of-wtc-symbol-set
                            (xs (union-equal
                                 (wtc-symbol-set features)
                                 (pp-action-provides action)))))
           :in-theory (e/d (pp-action-apply)
                           (no-duplicatesp-equal-of-wtc-symbol-set)))))

(defthm pp-action-apply-preserves-old-feature
  (implies (and (symbolp feature)
                (member-equal feature (wtc-symbol-set features)))
           (member-equal feature
                         (pp-action-apply action features))))

(defthm pp-action-apply-provides-feature
  (implies (member-equal feature (pp-action-provides action))
           (member-equal feature
                         (pp-action-apply action features))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Plans: feasibility, feature flow, and cost
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pp-plan-validp (plan)
  (if (endp plan)
      t
    (and (pp-action-validp (car plan))
         (pp-plan-validp (cdr plan)))))

(defun pp-plan-feasiblep (plan features)
  (if (endp plan)
      t
    (and (pp-action-enabledp (car plan) features)
         (pp-plan-feasiblep
          (cdr plan)
          (pp-action-apply (car plan) features)))))

(defun pp-plan-result (plan features)
  (if (endp plan)
      (wtc-symbol-set features)
    (pp-plan-result
     (cdr plan)
     (pp-action-apply (car plan) features))))

(defun pp-plan-cost (plan)
  (if (endp plan)
      (pp-cost 0 0 0 0 0)
    (pp-cost+ (pp-action-cost (car plan))
              (pp-plan-cost (cdr plan)))))

(defun pp-plan-kinds (plan)
  (if (endp plan)
      nil
    (cons (pp-action-kind (car plan))
          (pp-plan-kinds (cdr plan)))))

(defthm symbol-listp-of-pp-plan-result
  (symbol-listp (pp-plan-result plan features)))

(defthm no-duplicatesp-equal-of-pp-plan-result
  (no-duplicatesp-equal (pp-plan-result plan features)))

(defthm pp-costp-of-pp-plan-cost
  (pp-costp (pp-plan-cost plan)))

(defthm pp-plan-result-preserves-feature
  (implies (and (symbolp feature)
                (member-equal feature (wtc-symbol-set features)))
           (member-equal feature
                         (pp-plan-result plan features))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Replay receipts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pp-make-receipt (plan initial-features)
  (list :proof-plan-receipt
        plan
        initial-features
        (pp-plan-result plan initial-features)
        (pp-plan-cost plan)))

(defun pp-receipt-plan (receipt)
  (cadr receipt))

(defun pp-receipt-initial-features (receipt)
  (caddr receipt))

(defun pp-receipt-final-features (receipt)
  (cadddr receipt))

(defun pp-receipt-cost (receipt)
  (car (cddddr receipt)))

(defun pp-receipt-validp (receipt)
  (and (true-listp receipt)
       (equal (len receipt) 5)
       (eq (car receipt) :proof-plan-receipt)
       (pp-plan-validp (pp-receipt-plan receipt))
       (symbol-listp (pp-receipt-final-features receipt))
       (no-duplicatesp-equal (pp-receipt-final-features receipt))
       (pp-costp (pp-receipt-cost receipt))
       (pp-plan-feasiblep
        (pp-receipt-plan receipt)
        (pp-receipt-initial-features receipt))
       (equal (pp-receipt-final-features receipt)
              (pp-plan-result
               (pp-receipt-plan receipt)
               (pp-receipt-initial-features receipt)))
       (equal (pp-receipt-cost receipt)
              (pp-plan-cost (pp-receipt-plan receipt)))))

(defthm pp-receipt-plan-of-pp-make-receipt
  (equal (pp-receipt-plan
          (pp-make-receipt plan initial-features))
         plan))

(defthm pp-receipt-initial-of-pp-make-receipt
  (equal (pp-receipt-initial-features
          (pp-make-receipt plan initial-features))
         initial-features))

(defthm pp-receipt-final-of-pp-make-receipt
  (equal (pp-receipt-final-features
          (pp-make-receipt plan initial-features))
         (pp-plan-result plan initial-features)))

(defthm pp-receipt-cost-of-pp-make-receipt
  (equal (pp-receipt-cost
          (pp-make-receipt plan initial-features))
         (pp-plan-cost plan)))

(defthm pp-receipt-validp-of-pp-make-receipt
  (implies (and (pp-plan-validp plan)
                (pp-plan-feasiblep plan initial-features))
           (pp-receipt-validp
            (pp-make-receipt plan initial-features))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Executable pressure test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *pp-example-plan*
  '((:theory shape-capsule
             nil
             (shape-known)
             (0 1 60 4 1))
    (:induct list-recursion
             (shape-known)
             (induction-chosen)
             (0 2 120 2 1))
    (:linear arithmetic-close
             (induction-chosen)
             (goal-closed)
             (0 0 40 3 0))))

(assert-event (pp-plan-validp *pp-example-plan*))
(assert-event (pp-plan-feasiblep *pp-example-plan* nil))
(assert-event
 (equal (pp-plan-result *pp-example-plan* nil)
        '(shape-known induction-chosen goal-closed)))
(assert-event
 (equal (pp-plan-cost *pp-example-plan*)
        '(0 3 220 9 2)))
(assert-event
 (pp-receipt-validp (pp-make-receipt *pp-example-plan* nil)))
