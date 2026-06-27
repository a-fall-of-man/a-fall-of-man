; zaa-algebraic-dynamic-programming.lisp
;
; Finite acyclic weighted deduction over an abstract commutative semiring.
; A small rule system denotes an exponentially branching derivation tree,
; while the chart evaluator computes every item exactly once.

(in-package "ACL2")

(include-book "zlx-certified-parallel-fold")
(include-book "tools/def-functional-instance" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zaa-algebraic-dynamic-programming
  :parents (acl2::top)
  :short "A certified algebraic dynamic-programming kernel."
  :long
  "<p>A program is a topologically ordered list of weighted deductions.  Each
  item has a seed value and a list of rules.  A rule contributes its weight
  multiplied by the values of its premises; alternative rules are added.</p>

  <p>The recursive denotation unfolds all sharing into derivation trees.  The
  chart evaluator instead computes each item once and reuses it.  The main
  theorem proves the two meanings equal for every well-ranked program.  A
  separate instrumented evaluator proves an exact count of semiring operations.
  Existing certified parallel-fold mathematics is imported by functional
  instantiation for both rule alternatives and premise products.</p>

  <p><tt>ADP-FAST-VALUE</tt> is the forward executable implementation.  It
  traverses the program and every rule exactly once while storing completed
  items in an ACL2 fast alist.  <tt>ADP-FAST-VALUE-CORRECT</tt> refines this
  implementation to the derivation-tree denotation.  Under the ordinary
  expected-cost model for hash-table lookup, its administrative work is linear
  in the number of items, rules, and premise occurrences.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Abstract commutative semiring
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((adp-valuep *) => *)
   ((adp-zero) => *)
   ((adp-one) => *)
   ((adp-plus * *) => *)
   ((adp-times * *) => *))

  (local (defun adp-valuep (x) (natp x)))
  (local (defun adp-zero () 0))
  (local (defun adp-one () 1))
  (local (defun adp-plus (x y) (+ x y)))
  (local (defun adp-times (x y) (* x y)))

  (defthm adp-valuep-of-zero
    (adp-valuep (adp-zero)))
  (defthm adp-valuep-of-one
    (adp-valuep (adp-one)))
  (defthm adp-valuep-of-plus
    (implies (and (adp-valuep x) (adp-valuep y))
             (adp-valuep (adp-plus x y))))
  (defthm adp-valuep-of-times
    (implies (and (adp-valuep x) (adp-valuep y))
             (adp-valuep (adp-times x y))))

  (defthm adp-plus-associative
    (implies (and (adp-valuep x) (adp-valuep y) (adp-valuep z))
             (equal (adp-plus (adp-plus x y) z)
                    (adp-plus x (adp-plus y z)))))
  (defthm adp-plus-commutative
    (implies (and (adp-valuep x) (adp-valuep y))
             (equal (adp-plus x y) (adp-plus y x))))
  (defthm adp-plus-left-identity
    (implies (adp-valuep x)
             (equal (adp-plus (adp-zero) x) x)))
  (defthm adp-plus-right-identity
    (implies (adp-valuep x)
             (equal (adp-plus x (adp-zero)) x)))

  (defthm adp-times-associative
    (implies (and (adp-valuep x) (adp-valuep y) (adp-valuep z))
             (equal (adp-times (adp-times x y) z)
                    (adp-times x (adp-times y z)))))
  (defthm adp-times-commutative
    (implies (and (adp-valuep x) (adp-valuep y))
             (equal (adp-times x y) (adp-times y x))))
  (defthm adp-times-left-identity
    (implies (adp-valuep x)
             (equal (adp-times (adp-one) x) x)))
  (defthm adp-times-right-identity
    (implies (adp-valuep x)
             (equal (adp-times x (adp-one)) x)))
  (defthm adp-times-zero-left
    (implies (adp-valuep x)
             (equal (adp-times (adp-zero) x) (adp-zero))))
  (defthm adp-times-zero-right
    (implies (adp-valuep x)
             (equal (adp-times x (adp-zero)) (adp-zero))))

  (defthm adp-times-distributes-over-plus-left
    (implies (and (adp-valuep x) (adp-valuep y) (adp-valuep z))
             (equal (adp-times x (adp-plus y z))
                    (adp-plus (adp-times x y)
                              (adp-times x z)))))
  (defthm adp-times-distributes-over-plus-right
    (implies (and (adp-valuep x) (adp-valuep y) (adp-valuep z))
             (equal (adp-times (adp-plus x y) z)
                    (adp-plus (adp-times x z)
                              (adp-times y z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Parallelizable semiring folds, inherited from ZLX
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun adp-all-valuesp (xs)
  (if (endp xs)
      t
    (and (adp-valuep (car xs))
         (adp-all-valuesp (cdr xs)))))

(defthm adp-all-valuesp-of-append
  (equal (adp-all-valuesp (append xs ys))
         (and (adp-all-valuesp xs)
              (adp-all-valuesp ys)))
  :hints (("Goal"
           :induct (len xs)
           :in-theory (enable adp-all-valuesp))))

(defthm adp-plus-rotate-three
  (implies (and (adp-valuep x)
                (adp-valuep y)
                (adp-valuep z))
           (equal (adp-plus z (adp-plus x y))
                  (adp-plus x (adp-plus y z))))
  :hints (("Goal"
           :use ((:instance adp-plus-associative
                            (x z) (y x) (z y))
                 (:instance adp-plus-commutative
                            (x z) (y x))
                 (:instance adp-plus-associative
                            (x x) (y z) (z y))
                 (:instance adp-plus-commutative
                            (x z) (y y))))))

(defthm adp-times-rotate-three
  (implies (and (adp-valuep x)
                (adp-valuep y)
                (adp-valuep z))
           (equal (adp-times z (adp-times x y))
                  (adp-times x (adp-times y z))))
  :hints (("Goal"
           :use ((:instance adp-times-associative
                            (x z) (y x) (z y))
                 (:instance adp-times-commutative
                            (x z) (y x))
                 (:instance adp-times-associative
                            (x x) (y z) (z y))
                 (:instance adp-times-commutative
                            (x z) (y y))))))

(defun adp-flatten-blocks (blocks)
  (if (endp blocks)
      nil
    (append (car blocks)
            (adp-flatten-blocks (cdr blocks)))))

(defun adp-sum (xs)
  (if (endp xs)
      (adp-zero)
    (adp-plus (car xs) (adp-sum (cdr xs)))))

(defthm adp-valuep-of-sum
  (implies (adp-all-valuesp xs)
           (adp-valuep (adp-sum xs)))
  :hints (("Goal"
           :induct (adp-sum xs)
           :in-theory (e/d (adp-sum adp-all-valuesp)
                           (adp-plus-commutative
                            adp-plus-rotate-three)))))

(defthm adp-sum-of-append
  (implies (and (adp-all-valuesp xs)
                (adp-all-valuesp ys))
           (equal (adp-sum (append xs ys))
                  (adp-plus (adp-sum xs)
                            (adp-sum ys))))
  :hints (("Goal"
           :induct (adp-sum xs)
           :in-theory (e/d (adp-sum adp-all-valuesp)
                           (adp-plus-commutative
                            adp-plus-rotate-three)))))

(defun adp-sum-blocks (blocks)
  (if (endp blocks)
      (adp-zero)
    (adp-plus (adp-sum (car blocks))
              (adp-sum-blocks (cdr blocks)))))

(defun adp-product (xs)
  (if (endp xs)
      (adp-one)
    (adp-times (car xs) (adp-product (cdr xs)))))

(defthm adp-valuep-of-product
  (implies (adp-all-valuesp xs)
           (adp-valuep (adp-product xs)))
  :hints (("Goal"
           :induct (adp-product xs)
           :in-theory (e/d (adp-product adp-all-valuesp)
                           (adp-times-commutative
                            adp-times-rotate-three)))))

(defthm adp-product-of-append
  (implies (and (adp-all-valuesp xs)
                (adp-all-valuesp ys))
           (equal (adp-product (append xs ys))
                  (adp-times (adp-product xs)
                             (adp-product ys))))
  :hints (("Goal"
           :induct (adp-product xs)
           :in-theory (e/d (adp-product adp-all-valuesp)
                           (adp-times-commutative
                            adp-times-rotate-three)))))

(defun adp-product-blocks (blocks)
  (if (endp blocks)
      (adp-one)
    (adp-times (adp-product (car blocks))
               (adp-product-blocks (cdr blocks)))))

(def-functional-instance adp-sum-blocks-correct
  vpf-fold-blocks-correct
  ((vpf-carrierp adp-valuep)
   (vpf-op adp-plus)
   (vpf-id adp-zero)
   (vpf-all-carrierp adp-all-valuesp)
   (vpf-flatten-blocks adp-flatten-blocks)
   (vpf-fold adp-sum)
   (vpf-fold-blocks adp-sum-blocks)))

(def-functional-instance adp-product-blocks-correct
  vpf-fold-blocks-correct
  ((vpf-carrierp adp-valuep)
   (vpf-op adp-times)
   (vpf-id adp-one)
   (vpf-all-carrierp adp-all-valuesp)
   (vpf-flatten-blocks adp-flatten-blocks)
   (vpf-fold adp-product)
   (vpf-fold-blocks adp-product-blocks)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Weighted deduction programs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A rule is (weight . premise-indices).
; An item is (seed . rules).

(defun adp-premises-belowp (premises bound)
  (if (endp premises)
      t
    (and (natp (car premises))
         (< (car premises) (nfix bound))
         (adp-premises-belowp (cdr premises) bound))))

(defun adp-rule-validp (rule bound)
  (and (consp rule)
       (adp-valuep (car rule))
       (adp-premises-belowp (cdr rule) bound)))

(defun adp-rules-validp (rules bound)
  (if (endp rules)
      t
    (and (adp-rule-validp (car rules) bound)
         (adp-rules-validp (cdr rules) bound))))

(defun adp-item-validp (item bound)
  (and (consp item)
       (adp-valuep (car item))
       (adp-rules-validp (cdr item) bound)))

(defun adp-prefix-validp (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (adp-prefix-validp (1- n) program)
         (adp-item-validp (nth (1- n) program) (1- n)))))

(defun adp-program-validp (program)
  (adp-prefix-validp (len program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. One-pass chart evaluator
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun adp-chart-ref (index chart)
  (let ((look (assoc-equal (nfix index) chart)))
    (if look (cdr look) (adp-zero))))

(defun adp-eval-premises (premises chart)
  (if (endp premises)
      (adp-one)
    (adp-times (adp-chart-ref (car premises) chart)
               (adp-eval-premises (cdr premises) chart))))

(defun adp-eval-rule (rule chart)
  (adp-times (car rule)
             (adp-eval-premises (cdr rule) chart)))

(defun adp-eval-rules (rules chart)
  (if (endp rules)
      (adp-zero)
    (adp-plus (adp-eval-rule (car rules) chart)
              (adp-eval-rules (cdr rules) chart))))

(defun adp-eval-item (item chart)
  (adp-plus (car item)
            (adp-eval-rules (cdr item) chart)))

(defun adp-build-chart (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (let* ((index (1- n))
           (chart (adp-build-chart index program))
           (value (adp-eval-item (nth index program) chart)))
      (acons index value chart))))

(defun adp-run (program)
  (adp-build-chart (len program) program))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Recursive derivation-tree denotation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 (defun adp-denote-item (index program)
   (declare
    (xargs
     :measure
     (two-nats-measure
      (nfix index)
      (+ 1 (acl2-count (nth (nfix index) program))))))
   (let ((item (nth (nfix index) program)))
     (if (consp item)
         (adp-plus (car item)
                   (adp-denote-rules (cdr item) (nfix index) program))
       (adp-zero))))

 (defun adp-denote-rules (rules bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rules)))))
   (if (endp rules)
       (adp-zero)
     (adp-plus (adp-denote-rule (car rules) bound program)
               (adp-denote-rules (cdr rules) bound program))))

 (defun adp-denote-rule (rule bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count rule)))))
   (if (consp rule)
       (adp-times (car rule)
                  (adp-denote-premises (cdr rule) bound program))
     (adp-zero)))

 (defun adp-denote-premises (premises bound program)
   (declare
    (xargs
     :measure
     (two-nats-measure (nfix bound) (+ 1 (acl2-count premises)))))
   (if (endp premises)
       (adp-one)
     (if (and (natp (car premises))
              (< (car premises) (nfix bound)))
         (adp-times
          (adp-denote-item (car premises) program)
          (adp-denote-premises (cdr premises) bound program))
       (adp-zero)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Chart/denotation refinement
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun adp-chart-correctp (n chart program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (equal (adp-chart-ref (1- n) chart)
                (adp-denote-item (1- n) program))
         (adp-chart-correctp (1- n) chart program))))

(defthm adp-chart-ref-when-correct
  (implies (and (adp-chart-correctp n chart program)
                (natp index)
                (< index (nfix n)))
           (equal (adp-chart-ref index chart)
                  (adp-denote-item index program)))
  :hints (("Goal"
           :induct (adp-chart-correctp n chart program)
           :in-theory (enable adp-chart-correctp))))

(defthm adp-eval-premises-correct
  (implies (and (adp-premises-belowp premises bound)
                (adp-chart-correctp bound chart program))
           (equal (adp-eval-premises premises chart)
                  (adp-denote-premises premises bound program)))
  :hints (("Goal"
           :induct (adp-eval-premises premises chart)
           :in-theory (enable adp-eval-premises
                              adp-denote-premises
                              adp-premises-belowp))))

(defthm adp-eval-rule-correct
  (implies (and (adp-rule-validp rule bound)
                (adp-chart-correctp bound chart program))
           (equal (adp-eval-rule rule chart)
                  (adp-denote-rule rule bound program)))
  :hints (("Goal"
           :in-theory (enable adp-eval-rule
                              adp-denote-rule
                              adp-rule-validp))))

(defthm adp-eval-rules-correct
  (implies (and (adp-rules-validp rules bound)
                (adp-chart-correctp bound chart program))
           (equal (adp-eval-rules rules chart)
                  (adp-denote-rules rules bound program)))
  :hints (("Goal"
           :induct (adp-eval-rules rules chart)
           :in-theory (enable adp-eval-rules
                              adp-denote-rules
                              adp-rules-validp))))

(defthm adp-eval-item-correct
  (implies (and (adp-item-validp item bound)
                (adp-chart-correctp bound chart program))
           (equal (adp-eval-item item chart)
                  (adp-plus (car item)
                            (adp-denote-rules (cdr item) bound program))))
  :hints (("Goal"
           :in-theory (enable adp-eval-item adp-item-validp))))

(defthm adp-chart-ref-of-acons-same
  (equal (adp-chart-ref key (acons (nfix key) value chart))
         value)
  :hints (("Goal" :in-theory (enable adp-chart-ref))))

(defthm adp-chart-ref-of-acons-different
  (implies (not (equal (nfix key) (nfix other)))
           (equal (adp-chart-ref key (acons (nfix other) value chart))
                  (adp-chart-ref key chart)))
  :hints (("Goal" :in-theory (enable adp-chart-ref))))

(defthm adp-chart-correctp-of-acons-above
  (implies (and (adp-chart-correctp n chart program)
                (natp key)
                (<= (nfix n) key))
           (adp-chart-correctp n (acons key value chart) program))
  :hints (("Goal"
           :induct (adp-chart-correctp n chart program)
           :in-theory (enable adp-chart-correctp))))

(defthm adp-eval-nth-item-correct
  (implies (and (natp n)
                (adp-item-validp (nth n program) n)
                (adp-chart-correctp n chart program))
           (equal (adp-eval-item (nth n program) chart)
                  (adp-denote-item n program)))
  :hints (("Goal"
           :use ((:instance adp-eval-item-correct
                            (item (nth n program))
                            (bound n)))
           :in-theory (enable adp-denote-item
                              adp-item-validp))))

(defthm adp-chart-correctp-extend
  (implies (and (natp n)
                (adp-chart-correctp n chart program)
                (equal value (adp-denote-item n program)))
           (adp-chart-correctp
            (1+ n)
            (acons n value chart)
            program))
  :hints (("Goal"
           :use ((:instance adp-chart-correctp-of-acons-above
                            (key n)))
           :in-theory (enable adp-chart-correctp))))

(defthm adp-chart-correctp-extend-by-evaluation
  (implies (and (natp n)
                (adp-item-validp (nth n program) n)
                (adp-chart-correctp n chart program))
           (adp-chart-correctp
            (1+ n)
            (acons n
                   (adp-eval-item (nth n program) chart)
                   chart)
            program))
  :hints (("Goal"
           :use ((:instance adp-chart-correctp-extend
                            (value (adp-eval-item
                                    (nth n program)
                                    chart)))
                 (:instance adp-eval-nth-item-correct)))))

(defthm adp-build-chart-correct
  (implies (and (natp n)
                (adp-prefix-validp n program))
           (adp-chart-correctp n (adp-build-chart n program) program))
  :hints (("Goal"
           :induct (adp-build-chart n program)
           :in-theory (enable adp-build-chart
                              adp-prefix-validp))
          (and stable-under-simplificationp
               '(:use ((:instance
                        adp-chart-correctp-extend-by-evaluation
                        (n (1- n))
                        (chart (adp-build-chart (1- n) program))))))))

(defthm adp-run-correct
  (implies (and (adp-program-validp program)
                (natp index)
                (< index (len program)))
           (equal (adp-chart-ref index (adp-run program))
                  (adp-denote-item index program)))
  :hints (("Goal"
           :use ((:instance adp-chart-ref-when-correct
                            (n (len program))
                            (chart (adp-run program))))
           :in-theory (enable adp-run adp-program-validp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Exact semiring-operation accounting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun adp-premises-work (premises)
  (len premises))

(defun adp-rule-work (rule)
  (+ 1 (adp-premises-work (cdr rule))))

(defun adp-rules-work (rules)
  (if (endp rules)
      0
    (+ 1
       (adp-rule-work (car rules))
       (adp-rules-work (cdr rules)))))

(defun adp-item-work (item)
  (+ 1 (adp-rules-work (cdr item))))

(defun adp-prefix-work (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (adp-prefix-work (1- n) program)
       (adp-item-work (nth (1- n) program)))))

(defun adp-program-work (program)
  (adp-prefix-work (len program) program))

(defun adp-eval-premises$ (premises chart)
  (if (endp premises)
      (mv (adp-one) 0)
    (mv-let (rest-value rest-work)
      (adp-eval-premises$ (cdr premises) chart)
      (mv (adp-times (adp-chart-ref (car premises) chart)
                     rest-value)
          (1+ rest-work)))))

(defun adp-eval-rule$ (rule chart)
  (mv-let (premise-value premise-work)
    (adp-eval-premises$ (cdr rule) chart)
    (mv (adp-times (car rule) premise-value)
        (1+ premise-work))))

(defun adp-eval-rules$ (rules chart)
  (if (endp rules)
      (mv (adp-zero) 0)
    (mv-let (rule-value rule-work)
      (adp-eval-rule$ (car rules) chart)
      (mv-let (rest-value rest-work)
        (adp-eval-rules$ (cdr rules) chart)
        (mv (adp-plus rule-value rest-value)
            (+ 1 rule-work rest-work))))))

(defun adp-eval-item$ (item chart)
  (mv-let (rules-value rules-work)
    (adp-eval-rules$ (cdr item) chart)
    (mv (adp-plus (car item) rules-value)
        (1+ rules-work))))

(defun adp-build-chart$ (n program)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (mv nil 0)
    (let ((index (1- n)))
      (mv-let (chart previous-work)
        (adp-build-chart$ index program)
        (mv-let (value item-work)
          (adp-eval-item$ (nth index program) chart)
          (mv (acons index value chart)
              (+ previous-work item-work)))))))

(defun adp-run$ (program)
  (adp-build-chart$ (len program) program))

(defthm adp-eval-premises$-value
  (equal (mv-nth 0 (adp-eval-premises$ premises chart))
         (adp-eval-premises premises chart))
  :hints (("Goal"
           :induct (adp-eval-premises$ premises chart)
           :in-theory (enable adp-eval-premises$
                              adp-eval-premises))))

(defthm adp-eval-premises$-work
  (equal (mv-nth 1 (adp-eval-premises$ premises chart))
         (adp-premises-work premises))
  :hints (("Goal"
           :induct (adp-eval-premises$ premises chart)
           :in-theory (enable adp-eval-premises$
                              adp-premises-work))))

(defthm adp-eval-rule$-value
  (equal (mv-nth 0 (adp-eval-rule$ rule chart))
         (adp-eval-rule rule chart))
  :hints (("Goal"
           :in-theory (enable adp-eval-rule$
                              adp-eval-rule))))

(defthm adp-eval-rule$-work
  (equal (mv-nth 1 (adp-eval-rule$ rule chart))
         (adp-rule-work rule))
  :hints (("Goal"
           :in-theory (enable adp-eval-rule$
                              adp-rule-work))))

(defthm adp-eval-rules$-value
  (equal (mv-nth 0 (adp-eval-rules$ rules chart))
         (adp-eval-rules rules chart))
  :hints (("Goal"
           :induct (adp-eval-rules$ rules chart)
           :in-theory (enable adp-eval-rules$
                              adp-eval-rules))))

(defthm adp-eval-rules$-work
  (equal (mv-nth 1 (adp-eval-rules$ rules chart))
         (adp-rules-work rules))
  :hints (("Goal"
           :induct (adp-eval-rules$ rules chart)
           :in-theory (enable adp-eval-rules$
                              adp-rules-work))))

(defthm adp-eval-item$-value
  (equal (mv-nth 0 (adp-eval-item$ item chart))
         (adp-eval-item item chart))
  :hints (("Goal"
           :in-theory (enable adp-eval-item$
                              adp-eval-item))))

(defthm adp-eval-item$-work
  (equal (mv-nth 1 (adp-eval-item$ item chart))
         (adp-item-work item))
  :hints (("Goal"
           :in-theory (enable adp-eval-item$
                              adp-item-work))))

(defthm adp-build-chart$-value
  (equal (mv-nth 0 (adp-build-chart$ n program))
         (adp-build-chart n program))
  :hints (("Goal"
           :induct (adp-build-chart$ n program)
           :in-theory (enable adp-build-chart$
                              adp-build-chart))))

(defthm adp-build-chart$-work
  (equal (mv-nth 1 (adp-build-chart$ n program))
         (adp-prefix-work n program))
  :hints (("Goal"
           :induct (adp-build-chart$ n program)
           :in-theory (enable adp-build-chart$
                              adp-prefix-work))))

(defthm adp-run$-value
  (equal (mv-nth 0 (adp-run$ program))
         (adp-run program))
  :hints (("Goal" :in-theory (enable adp-run$ adp-run))))

(defthm adp-run$-exact-work
  (equal (mv-nth 1 (adp-run$ program))
         (adp-program-work program))
  :hints (("Goal"
           :use ((:instance adp-build-chart$-work
                            (n (len program))))
           :in-theory (e/d (adp-run$ adp-program-work)
                           (adp-build-chart$
                            adp-prefix-work)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 8. Forward hash-backed implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm adp-hons-assoc-equal-is-assoc-equal
  (implies (alistp chart)
           (equal (hons-assoc-equal key chart)
                  (assoc-equal key chart)))
  :hints (("Goal"
           :induct (hons-assoc-equal key chart)
           :in-theory (enable hons-assoc-equal
                              hons-equal
                              assoc-equal))))

(defun adp-fast-chart-ref (index chart)
  (let ((look (hons-get (nfix index) chart)))
    (if look (cdr look) (adp-zero))))

(defthm adp-fast-chart-ref-is-chart-ref
  (implies (alistp chart)
           (equal (adp-fast-chart-ref index chart)
                  (adp-chart-ref index chart)))
  :hints (("Goal"
           :in-theory (enable adp-fast-chart-ref
                              adp-chart-ref
                              hons-get))))

(defun adp-fast-eval-premises (premises chart)
  (if (endp premises)
      (adp-one)
    (adp-times (adp-fast-chart-ref (car premises) chart)
               (adp-fast-eval-premises (cdr premises) chart))))

(defun adp-fast-eval-rule (rule chart)
  (adp-times (car rule)
             (adp-fast-eval-premises (cdr rule) chart)))

(defun adp-fast-eval-rules (rules chart)
  (if (endp rules)
      (adp-zero)
    (adp-plus (adp-fast-eval-rule (car rules) chart)
              (adp-fast-eval-rules (cdr rules) chart))))

(defun adp-fast-eval-item (item chart)
  (adp-plus (car item)
            (adp-fast-eval-rules (cdr item) chart)))

(defthm adp-fast-eval-premises-is-eval-premises
  (implies (alistp chart)
           (equal (adp-fast-eval-premises premises chart)
                  (adp-eval-premises premises chart)))
  :hints (("Goal"
           :induct (adp-fast-eval-premises premises chart)
           :in-theory (enable adp-fast-eval-premises
                              adp-eval-premises))))

(defthm adp-fast-eval-rule-is-eval-rule
  (implies (alistp chart)
           (equal (adp-fast-eval-rule rule chart)
                  (adp-eval-rule rule chart)))
  :hints (("Goal"
           :in-theory (enable adp-fast-eval-rule
                              adp-eval-rule))))

(defthm adp-fast-eval-rules-is-eval-rules
  (implies (alistp chart)
           (equal (adp-fast-eval-rules rules chart)
                  (adp-eval-rules rules chart)))
  :hints (("Goal"
           :induct (adp-fast-eval-rules rules chart)
           :in-theory (enable adp-fast-eval-rules
                              adp-eval-rules))))

(defthm adp-fast-eval-item-is-eval-item
  (implies (alistp chart)
           (equal (adp-fast-eval-item item chart)
                  (adp-eval-item item chart)))
  :hints (("Goal"
           :in-theory (enable adp-fast-eval-item
                              adp-eval-item))))

(defun adp-fast-run-aux (items index chart)
  (if (endp items)
      chart
    (let ((value (adp-fast-eval-item (car items) chart)))
      (adp-fast-run-aux
       (cdr items)
       (1+ (nfix index))
       (hons-acons (nfix index) value chart)))))

(defun adp-fast-run (program)
  (adp-fast-run-aux program 0 nil))

(defun adp-fast-value (index program)
  (let* ((chart (adp-fast-run program))
         (value (adp-fast-chart-ref index chart)))
    (prog2$ (fast-alist-free chart)
            value)))

(defthm adp-cdr-of-nthcdr
  (equal (cdr (nthcdr n xs))
         (nthcdr (1+ (nfix n)) xs))
  :hints (("Goal"
           :induct (nthcdr n xs)
           :in-theory (enable nthcdr))))

(defthm adp-item-validp-when-prefix-valid
  (implies (and (natp n)
                (natp index)
                (< index n)
                (adp-prefix-validp n program))
           (adp-item-validp (nth index program) index))
  :hints (("Goal"
           :induct (adp-prefix-validp n program)
           :in-theory (enable adp-prefix-validp))))

(defthm adp-chart-correctp-extend-by-fast-evaluation
  (implies (and (natp n)
                (alistp chart)
                (adp-item-validp (nth n program) n)
                (adp-chart-correctp n chart program))
           (adp-chart-correctp
            (1+ n)
            (hons-acons n
                        (adp-fast-eval-item (nth n program) chart)
                        chart)
            program))
  :hints (("Goal"
           :use ((:instance adp-chart-correctp-extend-by-evaluation))
           :in-theory (enable hons-acons))))

(defthm adp-fast-current-item-valid
  (implies (and (natp index)
                (consp items)
                (equal items (nthcdr index program))
                (adp-prefix-validp (+ index (len items)) program))
           (adp-item-validp (car items) index))
  :hints (("Goal"
           :use ((:instance adp-item-validp-when-prefix-valid
                            (n (+ index (len items)))))
           :in-theory (disable adp-item-validp-when-prefix-valid))))

(defthm adp-chart-correctp-fast-step
  (implies (and (natp index)
                (consp items)
                (alistp chart)
                (equal items (nthcdr index program))
                (adp-prefix-validp (+ index (len items)) program)
                (adp-chart-correctp index chart program))
           (adp-chart-correctp
            (1+ index)
            (hons-acons index
                        (adp-fast-eval-item (car items) chart)
                        chart)
            program))
  :hints (("Goal"
           :use ((:instance adp-fast-current-item-valid)
                 (:instance
                  adp-chart-correctp-extend-by-fast-evaluation
                  (n index)))
           :in-theory
           (disable adp-fast-current-item-valid
                    adp-chart-correctp-extend-by-fast-evaluation
                    adp-chart-correctp
                    adp-denote-item
                    adp-eval-item
                    adp-fast-eval-item
                    adp-item-validp
                    adp-prefix-validp))))

(defthm adp-fast-run-aux-correct
  (implies
   (and (natp index)
        (alistp chart)
        (equal items (nthcdr index program))
        (adp-prefix-validp (+ index (len items)) program)
        (adp-chart-correctp index chart program))
   (adp-chart-correctp
    (+ index (len items))
    (adp-fast-run-aux items index chart)
    program))
  :hints (("Goal"
           :induct (adp-fast-run-aux items index chart)
           :in-theory (e/d (adp-fast-run-aux)
                           (adp-chart-correctp-fast-step
                            adp-chart-correctp-extend-by-fast-evaluation
                            adp-fast-current-item-valid
                            adp-item-validp-when-prefix-valid)))
          ("Subgoal *1/2"
           :use ((:instance adp-chart-correctp-fast-step)))))

(defthm adp-alistp-of-fast-run-aux
  (implies (alistp chart)
           (alistp (adp-fast-run-aux items index chart)))
  :hints (("Goal"
           :induct (adp-fast-run-aux items index chart)
           :in-theory (enable adp-fast-run-aux hons-acons))))

(defthm adp-alistp-of-fast-run
  (alistp (adp-fast-run program))
  :hints (("Goal" :in-theory (enable adp-fast-run))))

(defthm adp-fast-run-correct-chart
  (implies (adp-program-validp program)
           (adp-chart-correctp
            (len program)
            (adp-fast-run program)
            program))
  :hints (("Goal"
           :use ((:instance adp-fast-run-aux-correct
                            (items program)
                            (index 0)
                            (chart nil)))
           :in-theory (enable adp-fast-run
                              adp-program-validp
                              adp-chart-correctp))))

(defthm adp-fast-value-correct
  (implies (and (adp-program-validp program)
                (natp index)
                (< index (len program)))
           (equal (adp-fast-value index program)
                  (adp-denote-item index program)))
  :hints (("Goal"
           :use ((:instance adp-fast-run-correct-chart)
                 (:instance adp-chart-ref-when-correct
                            (n (len program))
                            (chart (adp-fast-run program))))
           :in-theory
           (e/d (adp-fast-value)
                (adp-fast-run-correct-chart
                 adp-chart-ref-when-correct)))))

(defxdoc adp-client-interface
  :parents (zaa-algebraic-dynamic-programming)
  :short "The small interface for building certified dynamic programs."
  :long
  "<p>Clients provide only a topologically ordered program of seeds and
  weighted rules.  The reusable payload is:</p>
  <ul>
   <li><tt>ADP-RUN-CORRECT</tt>: chart evaluation equals recursive derivation
       semantics;</li>
   <li><tt>ADP-RUN$-EXACT-WORK</tt>: exact semiring-operation count;</li>
   <li><tt>ADP-FAST-VALUE-CORRECT</tt>: the forward fast-alist executor equals
       the recursive derivation-tree meaning;</li>
   <li><tt>ADP-SUM-BLOCKS-CORRECT</tt> and
       <tt>ADP-PRODUCT-BLOCKS-CORRECT</tt>: arbitrary certified parallel
       decomposition of alternatives and premises.</li>
  </ul>")
