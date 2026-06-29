; zdc-adp-proof-plan-optimizer.lisp
;
; Compile a finite topologically ranked proof-plan graph into the already
; certified min-plus ranked shortest-path engine.  The optimizer returns the
; cheapest plan in the supplied graph and retains its action sequence as
; provenance.  This is finite-graph optimality, not completeness of ACL2 proof
; search.

(in-package "ACL2")

(include-book "zdb-proof-plan-semantics")
(include-book "zai-ranked-shortest-path-interface")
(include-book "xdoc/top" :dir :system)

(defxdoc zdc-adp-proof-plan-optimizer
  :parents (zdb-proof-plan-semantics)
  :short "ADP optimization of finite ranked proof-plan graphs with provenance."
  :long
  "<p>An optimizer item is <tt>(node features arc...)</tt>, where each arc is
  <tt>(predecessor-index action)</tt>.  Compilation replaces each action by the
  scalar product of its five-coordinate cost with a client-supplied weight
  vector, producing a ranked shortest-path instance.  The existing certified
  min-plus ADP compiler then returns a globally cheapest path in this finite
  graph.</p>

  <p>The selected path is translated back to the exact proof actions attached
  to its edges.  A receipt carries both the optimal weighted path certificate
  and this action provenance.  No theorem-proving soundness is attributed to
  the actions; later books still submit an ordinary theorem event to ACL2.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Ranked proof-plan graph syntax and compilation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ppo-item-node (item)
  (symbol-fix (car item)))

(defun ppo-item-features (item)
  (wtc-symbol-set (cadr item)))

(defun ppo-item-arcs (item)
  (cddr item))

(defun ppo-arc-pred (arc)
  (nfix (car arc)))

(defun ppo-arc-action (arc)
  (cadr arc))

(defun ppo-node-at (index spec)
  (ppo-item-node (nth (nfix index) spec)))

(defun ppo-features-at (index spec)
  (ppo-item-features (nth (nfix index) spec)))

(defun ppo-arc-score (arc weights)
  (pp-cost-score weights
                 (pp-action-cost (ppo-arc-action arc))))

(defun ppo-compile-arc (arc weights)
  (list (ppo-arc-pred arc)
        (ppo-arc-score arc weights)))

(defun ppo-compile-arcs (arcs weights)
  (if (endp arcs)
      nil
    (cons (ppo-compile-arc (car arcs) weights)
          (ppo-compile-arcs (cdr arcs) weights))))

(defun ppo-compile-item (item weights)
  (cons (ppo-item-node item)
        (ppo-compile-arcs (ppo-item-arcs item) weights)))

(defun ppo-compile-spec (spec weights)
  (if (endp spec)
      nil
    (cons (ppo-compile-item (car spec) weights)
          (ppo-compile-spec (cdr spec) weights))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Semantic graph checks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ppo-arc-semanticp (arc destination-features bound spec)
  (let* ((pred (ppo-arc-pred arc))
         (action (ppo-arc-action arc))
         (source-features (ppo-features-at pred spec)))
    (and (true-listp arc)
         (equal (len arc) 2)
         (natp (car arc))
         (< pred (nfix bound))
         (pp-action-validp action)
         (pp-action-enabledp action source-features)
         (subsetp-equal (pp-action-apply action source-features)
                        destination-features))))

(defun ppo-arcs-semanticp (arcs destination-features bound spec)
  (if (endp arcs)
      t
    (and (ppo-arc-semanticp (car arcs)
                            destination-features bound spec)
         (ppo-arcs-semanticp (cdr arcs)
                             destination-features bound spec))))

(defun ppo-prefix-semanticp (n spec)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (let* ((index (1- n))
           (item (nth index spec)))
      (and (ppo-prefix-semanticp index spec)
           (symbolp (car item))
           (symbol-listp (cadr item))
           (no-duplicatesp-equal (cadr item))
           (ppo-arcs-semanticp (ppo-item-arcs item)
                               (ppo-item-features item)
                               index spec)))))

(defun ppo-spec-validp (spec weights)
  (and (pp-costp (pp-cost-fix weights))
       (ppo-prefix-semanticp (len spec) spec)
       (rsp-spec-validp (ppo-compile-spec spec weights))))

(defthm ppo-spec-validp-implies-rsp-spec-validp
  (implies (ppo-spec-validp spec weights)
           (rsp-spec-validp (ppo-compile-spec spec weights)))
  :hints (("Goal" :in-theory (e/d (ppo-spec-validp)
                                      (rsp-spec-validp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Selected solution and action provenance
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ppo-solve (spec weights)
  (rsp-solve-final (ppo-compile-spec spec weights)))

(defun ppo-selected-score (spec weights)
  (rsp-solution-cost (ppo-solve spec weights)))

(defun ppo-selected-path (spec weights)
  (rsp-solution-path (ppo-solve spec weights)))

(defun ppo-selected-potentials (spec weights)
  (rsp-solution-potentials (ppo-solve spec weights)))

(defun ppo-find-item (node spec)
  (if (endp spec)
      nil
    (if (equal (ppo-item-node (car spec))
               (symbol-fix node))
        (car spec)
      (ppo-find-item node (cdr spec)))))

(defun ppo-find-action-in-arcs (from arcs spec)
  (if (endp arcs)
      nil
    (if (equal (ppo-node-at (ppo-arc-pred (car arcs)) spec)
               (symbol-fix from))
        (ppo-arc-action (car arcs))
      (ppo-find-action-in-arcs from (cdr arcs) spec))))

(defun ppo-action-for-edge (edge spec)
  (let ((item (ppo-find-item (vwc-edge->to edge) spec)))
    (ppo-find-action-in-arcs (vwc-edge->from edge)
                             (ppo-item-arcs item)
                             spec)))

(defun ppo-actions-for-path (path spec)
  (if (endp path)
      nil
    (cons (ppo-action-for-edge (car path) spec)
          (ppo-actions-for-path (cdr path) spec))))

(defun ppo-selected-actions (spec weights)
  (ppo-actions-for-path (ppo-selected-path spec weights) spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Optimal receipts and inherited global optimality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ppo-make-receipt (spec weights)
  (list :adp-proof-plan-receipt
        (vwc-path-cost (ppo-selected-path spec weights))
        (ppo-selected-path spec weights)
        (ppo-selected-actions spec weights)
        (ppo-selected-potentials spec weights)))

(defun ppo-receipt-optimalp (receipt spec weights)
  (and (true-listp receipt)
       (equal (len receipt) 5)
       (eq (car receipt) :adp-proof-plan-receipt)
       (equal (cadr receipt)
              (vwc-path-cost (caddr receipt)))
       (equal (cadddr receipt)
              (ppo-actions-for-path (caddr receipt) spec))
       (mwp-optimal-certificate-p
        (caddr receipt)
        (rsp-graph (ppo-compile-spec spec weights))
        (rsp-node-at 0 (ppo-compile-spec spec weights))
        (rsp-node-at
         (rsp-final-index (ppo-compile-spec spec weights))
         (ppo-compile-spec spec weights))
        (car (cddddr receipt)))))

(defthm ppo-selected-score-is-globally-optimal
  (implies
   (and
    (ppo-spec-validp spec weights)
    (vwc-certificate-p
     competitor
     (rsp-graph (ppo-compile-spec spec weights))
     (rsp-node-at 0 (ppo-compile-spec spec weights))
     (rsp-node-at
      (rsp-final-index (ppo-compile-spec spec weights))
      (ppo-compile-spec spec weights))))
   (<= (ppo-selected-score spec weights)
       (vwc-path-cost competitor)))
  :hints
  (("Goal"
    :expand ((ppo-selected-score spec weights)
             (ppo-solve spec weights))
    :use
    ((:instance ppo-spec-validp-implies-rsp-spec-validp)
     (:instance rsp-solve-final-answer-is-globally-optimal
                (spec (ppo-compile-spec spec weights))))
    :in-theory nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Executable ranked-plan pressure test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *ppo-step-weights* '(0 0 1 0 0))

(defconst *ppo-example-spec*
  '((start nil)
    (shape (shape-known)
           (0 (:theory shape-capsule
                       nil (shape-known) (0 1 60 4 1))))
    (induct (shape-known induction-chosen)
            (1 (:induct list-recursion
                        (shape-known)
                        (induction-chosen)
                        (0 2 120 2 1))))
    (broad (goal-closed)
           (0 (:theory ambient-theory
                       nil (goal-closed) (1 6 500 80 8))))
    (goal (shape-known induction-chosen goal-closed)
          (2 (:linear arithmetic-close
                      (induction-chosen)
                      (goal-closed)
                      (0 0 40 3 0)))
          (3 (:theory finish
                      (goal-closed)
                      (shape-known induction-chosen goal-closed)
                      (0 0 0 0 0))))))

(assert-event (ppo-spec-validp *ppo-example-spec* *ppo-step-weights*))
(assert-event
 (equal (ppo-selected-score *ppo-example-spec* *ppo-step-weights*)
        220))
(assert-event
 (equal (pp-plan-kinds
         (ppo-selected-actions *ppo-example-spec* *ppo-step-weights*))
        '(:theory :induct :linear)))
(assert-event
 (ppo-receipt-optimalp
  (ppo-make-receipt *ppo-example-spec* *ppo-step-weights*)
  *ppo-example-spec* *ppo-step-weights*))
