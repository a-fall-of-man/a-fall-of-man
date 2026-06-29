; zda-waterfall-theory-capsules.lisp
;
; A finite, executable semantics for ranked proof-theory capsules.  Capsules
; name small rune packets, import only earlier capsules, and locally subtract
; exclusions.  The result is a deterministic theory value that can be handed
; to ACL2's ordinary :in-theory hint without trusting the capsule compiler.

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zda-waterfall-theory-capsules
  :parents (acl2::top)
  :short "Ranked, compositional rune packets for waterfall-facing proofs."
  :long
  "<p>A capsule is <tt>(name own-runes exclusions dependencies)</tt>.  Its
  dependencies are indices of earlier capsules, so compilation is a single
  forward fold.  The effective theory is the duplicate-free union of the
  capsule's own runes and the already-compiled dependency theories, followed
  by local exclusion.</p>

  <p>The compiler is only a hint constructor.  Its output has no trusted role:
  ACL2's ordinary prover must still admit any theorem using the resulting
  theory.  The logical results below establish closure hygiene, direct-rule
  preservation, dependency preservation, and exclusion noninterference.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Total finite-set normalizers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wtc-symbol-filter (xs)
  (if (endp xs)
      nil
    (if (symbolp (car xs))
        (cons (car xs) (wtc-symbol-filter (cdr xs)))
      (wtc-symbol-filter (cdr xs)))))

(defun wtc-symbol-set (xs)
  (remove-duplicates-equal (wtc-symbol-filter xs)))

(defun wtc-nat-filter (xs)
  (if (endp xs)
      nil
    (if (natp (car xs))
        (cons (car xs) (wtc-nat-filter (cdr xs)))
      (wtc-nat-filter (cdr xs)))))

(defun wtc-nat-set (xs)
  (remove-duplicates-equal (wtc-nat-filter xs)))

(defthm symbol-listp-of-wtc-symbol-filter
  (symbol-listp (wtc-symbol-filter xs)))

(defthm symbol-listp-of-wtc-symbol-set
  (symbol-listp (wtc-symbol-set xs))
  :hints (("Goal" :in-theory (enable wtc-symbol-set))))

(defthm no-duplicatesp-equal-of-wtc-symbol-set
  (no-duplicatesp-equal (wtc-symbol-set xs))
  :hints (("Goal" :in-theory (enable wtc-symbol-set))))

(defthm nat-listp-of-wtc-nat-filter
  (nat-listp (wtc-nat-filter xs)))

(defthm nat-listp-of-wtc-nat-set
  (nat-listp (wtc-nat-set xs))
  :hints (("Goal" :in-theory (enable wtc-nat-set))))

(defthm no-duplicatesp-equal-of-wtc-nat-set
  (no-duplicatesp-equal (wtc-nat-set xs))
  :hints (("Goal" :in-theory (enable wtc-nat-set))))

(defthm member-of-wtc-symbol-filter
  (iff (member-equal rune (wtc-symbol-filter xs))
       (and (symbolp rune)
            (member-equal rune xs)))
  :hints (("Goal"
           :induct (wtc-symbol-filter xs)
           :in-theory (enable wtc-symbol-filter))))

(defthm member-of-wtc-symbol-set
  (iff (member-equal rune (wtc-symbol-set xs))
       (and (symbolp rune)
            (member-equal rune xs)))
  :hints (("Goal"
           :in-theory (enable wtc-symbol-set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Capsule syntax and ranked validity
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wtc-capsule-name (capsule)
  (symbol-fix (car capsule)))

(defun wtc-capsule-own-runes (capsule)
  (wtc-symbol-set (cadr capsule)))

(defun wtc-capsule-exclusions (capsule)
  (wtc-symbol-set (caddr capsule)))

(defun wtc-capsule-dependencies (capsule)
  (wtc-nat-set (cadddr capsule)))

(defthm nat-listp-of-wtc-capsule-dependencies
  (nat-listp (wtc-capsule-dependencies capsule))
  :hints (("Goal"
           :use ((:instance nat-listp-of-wtc-nat-set
                            (xs (cadddr capsule))))
           :in-theory (e/d (wtc-capsule-dependencies)
                           (nat-listp-of-wtc-nat-set)))))

(defun wtc-dependencies-belowp (dependencies bound)
  (if (endp dependencies)
      t
    (and (natp (car dependencies))
         (< (car dependencies) (nfix bound))
         (wtc-dependencies-belowp (cdr dependencies) bound))))

(defun wtc-capsule-validp (capsule bound)
  (and (true-listp capsule)
       (equal (len capsule) 4)
       (symbolp (car capsule))
       (symbol-listp (cadr capsule))
       (symbol-listp (caddr capsule))
       (nat-listp (cadddr capsule))
       (no-duplicatesp-equal (cadddr capsule))
       (wtc-dependencies-belowp (cadddr capsule) bound)))

(defun wtc-prefix-validp (n registry)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (wtc-prefix-validp (1- n) registry)
         (wtc-capsule-validp (nth (1- n) registry) (1- n)))))

(defun wtc-capsule-names (registry)
  (if (endp registry)
      nil
    (cons (wtc-capsule-name (car registry))
          (wtc-capsule-names (cdr registry)))))

(defun wtc-registry-validp (registry)
  (and (consp registry)
       (wtc-prefix-validp (len registry) registry)
       (no-duplicatesp-equal (wtc-capsule-names registry))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Forward capsule compilation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wtc-chart-ref (index chart)
  (let ((look (assoc-equal (nfix index) chart)))
    (if look
        (wtc-symbol-set (cdr look))
      nil)))

(defun wtc-gather-dependency-runes (dependencies chart)
  (if (endp dependencies)
      nil
    (union-equal
     (wtc-chart-ref (car dependencies) chart)
     (wtc-gather-dependency-runes (cdr dependencies) chart))))

(defun wtc-source-runes (capsule chart)
  (union-equal (wtc-capsule-own-runes capsule)
               (wtc-gather-dependency-runes
                (wtc-capsule-dependencies capsule)
                chart)))

(defun wtc-effective-runes (capsule chart)
  (wtc-symbol-set
   (set-difference-equal
    (wtc-source-runes capsule chart)
    (wtc-capsule-exclusions capsule))))

(defun wtc-compile-aux (capsules index chart)
  (if (endp capsules)
      chart
    (let ((theory (wtc-effective-runes (car capsules) chart)))
      (wtc-compile-aux
       (cdr capsules)
       (1+ (nfix index))
       (acons (nfix index) theory chart)))))

(defun wtc-compile (registry)
  (wtc-compile-aux registry 0 nil))

(defun wtc-final-index (registry)
  (if (consp registry)
      (1- (len registry))
    0))

(defun wtc-final-theory (registry)
  (wtc-chart-ref (wtc-final-index registry)
                 (wtc-compile registry)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Chart hygiene predicates and local closure laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun wtc-chart-symbol-listsp (chart)
  (if (endp chart)
      t
    (and (symbol-listp (cdar chart))
         (wtc-chart-symbol-listsp (cdr chart)))))

(defun wtc-chart-no-duplicatesp (chart)
  (if (endp chart)
      t
    (and (no-duplicatesp-equal (cdar chart))
         (wtc-chart-no-duplicatesp (cdr chart)))))

(defthm symbol-listp-of-wtc-chart-ref
  (symbol-listp (wtc-chart-ref index chart))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (cdr (assoc-equal (nfix index) chart)))))
           :in-theory (e/d (wtc-chart-ref)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm no-duplicatesp-equal-of-wtc-chart-ref
  (no-duplicatesp-equal (wtc-chart-ref index chart))
  :hints (("Goal"
           :use ((:instance no-duplicatesp-equal-of-wtc-symbol-set
                            (xs (cdr (assoc-equal (nfix index) chart)))))
           :in-theory (e/d (wtc-chart-ref)
                           (no-duplicatesp-equal-of-wtc-symbol-set)))))

(defthm wtc-symbol-listp-of-union-equal
  (implies (and (symbol-listp xs)
                (symbol-listp ys))
           (symbol-listp (union-equal xs ys)))
  :hints (("Goal"
           :induct (union-equal xs ys)
           :in-theory (enable union-equal))))

(defthm wtc-symbol-listp-of-set-difference-equal
  (implies (symbol-listp xs)
           (symbol-listp (set-difference-equal xs ys)))
  :hints (("Goal"
           :induct (set-difference-equal xs ys)
           :in-theory (enable set-difference-equal))))

(defthm symbol-listp-of-wtc-gather-dependency-runes
  (symbol-listp
   (wtc-gather-dependency-runes dependencies chart))
  :hints (("Goal"
           :induct (wtc-gather-dependency-runes dependencies chart)
           :in-theory (e/d (wtc-gather-dependency-runes)
                           (wtc-chart-ref
                            symbol-listp-of-wtc-chart-ref
                            wtc-symbol-listp-of-union-equal)))
          (and stable-under-simplificationp
               '(:use ((:instance symbol-listp-of-wtc-chart-ref
                                  (index (car dependencies)))
                        (:instance wtc-symbol-listp-of-union-equal
                                  (xs (wtc-chart-ref (car dependencies) chart))
                                  (ys (wtc-gather-dependency-runes
                                       (cdr dependencies) chart))))
                 :in-theory nil))))

(defthm symbol-listp-of-wtc-capsule-own-runes
  (symbol-listp (wtc-capsule-own-runes capsule))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (cadr capsule))))
           :in-theory (e/d (wtc-capsule-own-runes)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm symbol-listp-of-wtc-source-runes
  (symbol-listp (wtc-source-runes capsule chart))
  :hints (("Goal"
           :use ((:instance wtc-symbol-listp-of-union-equal
                            (xs (wtc-capsule-own-runes capsule))
                            (ys (wtc-gather-dependency-runes
                                 (wtc-capsule-dependencies capsule)
                                 chart))))
           :in-theory (e/d (wtc-source-runes)
                           (wtc-symbol-listp-of-union-equal
                            wtc-capsule-own-runes
                            wtc-capsule-dependencies
                            wtc-gather-dependency-runes)))))

(defthm symbol-listp-of-wtc-effective-runes
  (symbol-listp (wtc-effective-runes capsule chart))
  :hints (("Goal"
           :use ((:instance symbol-listp-of-wtc-symbol-set
                            (xs (set-difference-equal
                                 (wtc-source-runes capsule chart)
                                 (wtc-capsule-exclusions capsule)))))
           :in-theory (e/d (wtc-effective-runes)
                           (symbol-listp-of-wtc-symbol-set)))))

(defthm no-duplicatesp-equal-of-wtc-effective-runes
  (no-duplicatesp-equal (wtc-effective-runes capsule chart))
  :hints (("Goal"
           :use ((:instance no-duplicatesp-equal-of-wtc-symbol-set
                            (xs (set-difference-equal
                                 (wtc-source-runes capsule chart)
                                 (wtc-capsule-exclusions capsule)))))
           :in-theory (e/d (wtc-effective-runes)
                           (no-duplicatesp-equal-of-wtc-symbol-set)))))

(defthm wtc-exclusion-noninterference
  (implies (member-equal rune (wtc-capsule-exclusions capsule))
           (not (member-equal rune
                              (wtc-effective-runes capsule chart)))))

(defthm wtc-own-rune-preserved
  (implies (and (member-equal rune (wtc-capsule-own-runes capsule))
                (not (member-equal rune
                                   (wtc-capsule-exclusions capsule))))
           (member-equal rune (wtc-effective-runes capsule chart))))

(defthm wtc-member-of-gather-dependency-runes
  (implies
   (and (member-equal dependency dependencies)
        (member-equal rune (wtc-chart-ref dependency chart)))
   (member-equal rune
                 (wtc-gather-dependency-runes dependencies chart)))
  :hints (("Goal"
           :induct (wtc-gather-dependency-runes dependencies chart)
           :in-theory (e/d (wtc-gather-dependency-runes)
                           (wtc-chart-ref wtc-symbol-set)))))

(defthm wtc-dependency-rune-preserved
  (implies
   (and (symbolp rune)
        (member-equal dependency
                      (wtc-capsule-dependencies capsule))
        (member-equal rune (wtc-chart-ref dependency chart))
        (not (member-equal rune
                           (wtc-capsule-exclusions capsule))))
   (member-equal rune (wtc-effective-runes capsule chart)))
  :hints (("Goal"
           :use ((:instance wtc-member-of-gather-dependency-runes
                            (dependencies (wtc-capsule-dependencies capsule))))
           :in-theory (e/d (wtc-effective-runes
                            wtc-source-runes)
                           (wtc-member-of-gather-dependency-runes
                            wtc-capsule-dependencies
                            wtc-capsule-exclusions
                            wtc-chart-ref
                            wtc-gather-dependency-runes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Chart hygiene
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm wtc-chart-symbol-listsp-of-acons
  (equal (wtc-chart-symbol-listsp (acons key value chart))
         (and (symbol-listp value)
              (wtc-chart-symbol-listsp chart))))

(defthm wtc-chart-no-duplicatesp-of-acons
  (equal (wtc-chart-no-duplicatesp (acons key value chart))
         (and (no-duplicatesp-equal value)
              (wtc-chart-no-duplicatesp chart))))

(defthm wtc-chart-symbol-listsp-of-compile-aux
  (implies (wtc-chart-symbol-listsp chart)
           (wtc-chart-symbol-listsp
            (wtc-compile-aux capsules index chart)))
  :hints (("Goal"
           :induct (wtc-compile-aux capsules index chart)
           :in-theory (e/d (wtc-compile-aux)
                           (wtc-effective-runes
                            symbol-listp-of-wtc-effective-runes
                            wtc-chart-symbol-listsp-of-acons)))
          (and stable-under-simplificationp
               '(:use ((:instance symbol-listp-of-wtc-effective-runes
                                  (capsule (car capsules)))
                        (:instance wtc-chart-symbol-listsp-of-acons
                                  (key (nfix index))
                                  (value (wtc-effective-runes
                                          (car capsules) chart))))
                 :in-theory nil))))

(defthm wtc-chart-no-duplicatesp-of-compile-aux
  (implies (wtc-chart-no-duplicatesp chart)
           (wtc-chart-no-duplicatesp
            (wtc-compile-aux capsules index chart)))
  :hints (("Goal"
           :induct (wtc-compile-aux capsules index chart)
           :in-theory (e/d (wtc-compile-aux)
                           (wtc-effective-runes
                            no-duplicatesp-equal-of-wtc-effective-runes
                            wtc-chart-no-duplicatesp-of-acons)))
          (and stable-under-simplificationp
               '(:use ((:instance no-duplicatesp-equal-of-wtc-effective-runes
                                  (capsule (car capsules)))
                        (:instance wtc-chart-no-duplicatesp-of-acons
                                  (key (nfix index))
                                  (value (wtc-effective-runes
                                          (car capsules) chart))))
                 :in-theory nil))))

(defthm wtc-compiled-chart-hygienic
  (and (wtc-chart-symbol-listsp (wtc-compile registry))
       (wtc-chart-no-duplicatesp (wtc-compile registry))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Executable capsule pressure test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *wtc-example-registry*
  '((shape-base
     (consp car-cons cdr-cons)
     nil
     nil)
    (list-recursion
     (endp len)
     (consp)
     (0))
    (guarded-fold
     (true-listp append)
     (car-cons)
     (1))))

(assert-event (wtc-registry-validp *wtc-example-registry*))
(assert-event
 (equal (wtc-final-theory *wtc-example-registry*)
        '(true-listp append endp len cdr-cons)))

(defxdoc wtc-user-interface
  :parents (zda-waterfall-theory-capsules)
  :short "Public capsule compiler interface."
  :long
  "<p><tt>WTC-FINAL-THEORY</tt> compiles a ranked capsule registry to a
  duplicate-free symbol theory suitable for a quoted <tt>:IN-THEORY</tt> hint.
  <tt>WTC-REGISTRY-VALIDP</tt> checks topological dependencies and unique
  capsule names.  The final ACL2 theorem event remains the only trusted proof
  step.</p>")
