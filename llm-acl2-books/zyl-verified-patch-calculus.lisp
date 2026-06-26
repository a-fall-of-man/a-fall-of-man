; zyl-verified-patch-calculus.lisp
;
; A dependent ACL2 book over ZZE-EXOTIC-FERTILE-KERNEL.
;
; Theme: a small verified edit-script calculus whose inserted material is
; canonical RLE and whose output can be compiled directly into the affine
; cocycle summaries supplied by ZZE.
;
; This book intentionally contains no SKIP-PROOFS, DEFAXIOM, trust tags,
; program-mode definitions, raw Lisp, or generated events.  It is a first
; certification candidate: ACL2, not source inspection, decides admission.

(in-package "ACL2")

(include-book "zze-exotic-fertile-kernel")

(defxdoc zyl-verified-patch-calculus
  :parents (xef-exotic-fertile-kernel)
  :short "Canonical edit scripts with compressed insertions and cocycle summaries."
  :long
  "<p>This book defines a total edit-script language over ordinary ACL2
  lists.  A patch instruction either keeps source symbols, drops source
  symbols, or inserts a canonical run-length encoded word.  Patch execution
  reports whether every requested source span was available, the produced
  output, and the unconsumed source suffix.</p>

  <p>The normalization layer removes empty operations, merges adjacent keeps
  and drops, and joins adjacent insertions with <tt>XEF-RLE-JOIN</tt>.  The
  semantic layer compiles patch output directly to the affine cocycle monoid
  from <tt>ZZE-EXOTIC-FERTILE-KERNEL</tt>, avoiding construction of the complete
  output word when only its summary is needed.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Total prefix operations
;;
;; These functions use ACL2's total-list convention: a non-cons tail is the
;; end of the sequence.  Counts are normalized with NFIX.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-take (n xs)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (endp xs))
      nil
    (cons (car xs)
          (zyp-take (1- n) (cdr xs)))))

(defun zyp-drop-prefix (n xs)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n)
         xs)
        ((endp xs)
         nil)
        (t
         (zyp-drop-prefix (1- n) (cdr xs)))))

(defun zyp-enoughp (n xs)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (and (consp xs)
         (zyp-enoughp (1- n) (cdr xs)))))

(defthm zyp-append-take-and-drop
  (equal (append (zyp-take n xs)
                 (true-list-fix (zyp-drop-prefix n xs)))
         (true-list-fix xs))
  :hints
  (("Goal"
    :induct (zyp-take n xs)
    :in-theory (enable zyp-take zyp-drop-prefix))))

(defthm zyp-len-of-take-when-enough
  (implies (zyp-enoughp n xs)
           (equal (len (zyp-take n xs))
                  (nfix n)))
  :hints
  (("Goal"
    :induct (zyp-enoughp n xs)
    :in-theory (enable zyp-enoughp zyp-take))))

(defthm zyp-len-of-drop-when-enough
  (implies (zyp-enoughp n xs)
           (equal (len (zyp-drop-prefix n xs))
                  (- (len xs) (nfix n))))
  :hints
  (("Goal"
    :induct (zyp-enoughp n xs)
    :in-theory (enable zyp-enoughp zyp-drop-prefix))))

; Sequential prefix consumption is addition of counts.  These three laws are
; the algebra used later when adjacent KEEP or DROP instructions are fused.
(defthm zyp-drop-prefix-of-sum
  (equal (zyp-drop-prefix (+ (nfix m) (nfix n)) xs)
         (zyp-drop-prefix n (zyp-drop-prefix m xs)))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix m xs)
    :in-theory (enable zyp-drop-prefix))))

(defthm zyp-take-of-sum
  (equal (zyp-take (+ (nfix m) (nfix n)) xs)
         (append (zyp-take m xs)
                 (zyp-take n (zyp-drop-prefix m xs))))
  :hints
  (("Goal"
    :induct (zyp-take m xs)
    :in-theory (enable zyp-take zyp-drop-prefix))))

(defthm zyp-enoughp-of-sum
  (equal (zyp-enoughp (+ (nfix m) (nfix n)) xs)
         (and (zyp-enoughp m xs)
              (zyp-enoughp n (zyp-drop-prefix m xs))))
  :hints
  (("Goal"
    :induct (zyp-enoughp m xs)
    :in-theory (enable zyp-enoughp zyp-drop-prefix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Patch instructions
;;
;; Public constructors:
;;
;;   (ZYP-KEEP n)          retain and consume N source symbols
;;   (ZYP-DROP n)          discard and consume N source symbols
;;   (ZYP-INSERT runs)     emit the RLE word RUNS without consuming source
;;
;; The concrete representation is a two-element list.  Client books should
;; prefer the constructors, recognizers, and accessors below.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-keep (n)
  (list :keep (nfix n)))

(defun zyp-drop (n)
  (list :drop (nfix n)))

(defun zyp-insert (runs)
  (list :insert (xef-rle-canonicalize runs)))

(defun zyp-keep-p (instruction)
  (and (consp instruction)
       (equal (car instruction) :keep)
       (consp (cdr instruction))
       (endp (cddr instruction))))

(defun zyp-drop-p (instruction)
  (and (consp instruction)
       (equal (car instruction) :drop)
       (consp (cdr instruction))
       (endp (cddr instruction))))

(defun zyp-insert-p (instruction)
  (and (consp instruction)
       (equal (car instruction) :insert)
       (consp (cdr instruction))
       (endp (cddr instruction))))

(defun zyp-count (instruction)
  (nfix (cadr instruction)))

(defun zyp-insert-runs (instruction)
  (cadr instruction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. One-instruction semantics
;;
;; Malformed instructions are total no-ops.  They are not canonical, but
;; dropping them during normalization preserves all observable semantics.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-step-rest (instruction source)
  (cond ((zyp-keep-p instruction)
         (zyp-drop-prefix (zyp-count instruction) source))
        ((zyp-drop-p instruction)
         (zyp-drop-prefix (zyp-count instruction) source))
        (t
         source)))

(defun zyp-step-output (instruction source)
  (cond ((zyp-keep-p instruction)
         (zyp-take (zyp-count instruction) source))
        ((zyp-insert-p instruction)
         (xef-rle-decode (zyp-insert-runs instruction)))
        (t
         nil)))

(defun zyp-step-okp (instruction source)
  (cond ((zyp-keep-p instruction)
         (zyp-enoughp (zyp-count instruction) source))
        ((zyp-drop-p instruction)
         (zyp-enoughp (zyp-count instruction) source))
        (t
         t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Whole-patch semantics
;;
;; Execution is factored into three projections.  This makes sequencing
;; theorems small and lets later books use only the projection they need.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-patch-rest (patch source)
  (if (endp patch)
      (true-list-fix source)
    (zyp-patch-rest
     (cdr patch)
     (zyp-step-rest (car patch) source))))

(defun zyp-patch-output (patch source)
  (if (endp patch)
      nil
    (append
     (zyp-step-output (car patch) source)
     (zyp-patch-output
      (cdr patch)
      (zyp-step-rest (car patch) source)))))

(defun zyp-patch-okp (patch source)
  (if (endp patch)
      t
    (and (zyp-step-okp (car patch) source)
         (zyp-patch-okp
          (cdr patch)
          (zyp-step-rest (car patch) source)))))

(defun zyp-result (okp output rest)
  (list (if okp t nil)
        (true-list-fix output)
        (true-list-fix rest)))

(defun zyp-result-okp (result)
  (if (car result) t nil))

(defun zyp-result-output (result)
  (true-list-fix (cadr result)))

(defun zyp-result-rest (result)
  (true-list-fix (caddr result)))

(defun zyp-apply (patch source)
  (zyp-result (zyp-patch-okp patch source)
              (zyp-patch-output patch source)
              (zyp-patch-rest patch source)))

(defun zyp-result-seq (first second)
  (zyp-result (and (zyp-result-okp first)
                   (zyp-result-okp second))
              (append (zyp-result-output first)
                      (zyp-result-output second))
              (zyp-result-rest second)))

; The whole-patch sequencing law crosses a total-list normalization
; boundary at the empty patch.  These lemmas make that boundary an
; explicit semantic interface instead of asking the append proof to
; rediscover TRUE-LIST-FIX behavior inside recursive patch execution.

(defthm zyp-take-of-true-list-fix
  (equal (zyp-take n (true-list-fix source))
         (zyp-take n source))
  :hints
  (("Goal"
    :induct (zyp-take n source)
    :in-theory (enable zyp-take))))

(defthm zyp-enoughp-of-true-list-fix
  (equal (zyp-enoughp n (true-list-fix source))
         (zyp-enoughp n source))
  :hints
  (("Goal"
    :induct (zyp-enoughp n source)
    :in-theory (enable zyp-enoughp))))

(defthm zyp-drop-prefix-of-true-list-fix
  (equal (zyp-drop-prefix n (true-list-fix source))
         (true-list-fix (zyp-drop-prefix n source)))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n source)
    :in-theory (enable zyp-drop-prefix))))

(defthm zyp-step-rest-of-true-list-fix
  (equal (zyp-step-rest instruction (true-list-fix source))
         (true-list-fix (zyp-step-rest instruction source)))
  :hints
  (("Goal"
    :in-theory (enable zyp-step-rest))))

(defthm zyp-patch-rest-of-true-list-fix
  (equal (zyp-patch-rest patch (true-list-fix source))
         (zyp-patch-rest patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-rest patch source)
    :in-theory (enable zyp-patch-rest))))

(defthm zyp-step-output-of-true-list-fix
  (equal (zyp-step-output instruction (true-list-fix source))
         (zyp-step-output instruction source))
  :hints
  (("Goal"
    :in-theory (enable zyp-step-output))))

(defthm zyp-step-okp-of-true-list-fix
  (equal (zyp-step-okp instruction (true-list-fix source))
         (zyp-step-okp instruction source))
  :hints
  (("Goal"
    :in-theory (enable zyp-step-okp))))

(defthm zyp-patch-output-of-true-list-fix
  (equal (zyp-patch-output patch (true-list-fix source))
         (zyp-patch-output patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-output patch source)
    :in-theory (enable zyp-patch-output))))

(defthm zyp-patch-okp-of-true-list-fix
  (equal (zyp-patch-okp patch (true-list-fix source))
         (zyp-patch-okp patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-okp patch source)
    :in-theory (enable zyp-patch-okp))))

(defthm true-listp-of-zyp-patch-rest
  (true-listp (zyp-patch-rest patch source))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :induct (zyp-patch-rest patch source)
    :in-theory (enable zyp-patch-rest))))

(defthm zyp-patch-rest-of-append
  (equal (zyp-patch-rest (append left right) source)
         (zyp-patch-rest
          right
          (zyp-patch-rest left source)))
  :hints
  (("Goal"
    :induct (zyp-patch-rest left source)
    :in-theory
    (e/d (zyp-patch-rest
          zyp-patch-rest-of-true-list-fix)
         (zyp-step-rest
          zyp-drop-prefix)))))

(defthm zyp-patch-output-of-append
  (equal (zyp-patch-output (append left right) source)
         (append
          (zyp-patch-output left source)
          (zyp-patch-output
           right
           (zyp-patch-rest left source))))
  :hints
  (("Goal"
    :induct (zyp-patch-output left source)
    :in-theory
    (e/d (zyp-patch-output
          zyp-patch-rest
          zyp-patch-output-of-true-list-fix)
         (zyp-step-output
          zyp-step-rest)))))

(defthm zyp-patch-okp-of-append
  (equal (zyp-patch-okp (append left right) source)
         (and (zyp-patch-okp left source)
              (zyp-patch-okp
               right
               (zyp-patch-rest left source))))
  :hints
  (("Goal"
    :induct (zyp-patch-okp left source)
    :in-theory
    (e/d (zyp-patch-okp
          zyp-patch-rest
          zyp-patch-okp-of-true-list-fix)
         (zyp-step-okp
          zyp-step-rest)))))

(defthm zyp-apply-of-append
  (equal (zyp-apply (append left right) source)
         (zyp-result-seq
          (zyp-apply left source)
          (zyp-apply
           right
           (zyp-result-rest
            (zyp-apply left source)))))
  :hints
  (("Goal"
    :in-theory
    (enable zyp-apply
            zyp-result-seq
            zyp-result-okp
            zyp-result-output
            zyp-result-rest
            zyp-result))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Static accounting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-source-demand (patch)
  (if (endp patch)
      0
    (+ (cond ((zyp-keep-p (car patch))
              (zyp-count (car patch)))
             ((zyp-drop-p (car patch))
              (zyp-count (car patch)))
             (t 0))
       (zyp-source-demand (cdr patch)))))

(defun zyp-kept-length (patch)
  (if (endp patch)
      0
    (+ (if (zyp-keep-p (car patch))
           (zyp-count (car patch))
         0)
       (zyp-kept-length (cdr patch)))))

(defun zyp-inserted-length (patch)
  (if (endp patch)
      0
    (+ (if (zyp-insert-p (car patch))
           (xef-rle-symbol-count
            (zyp-insert-runs (car patch)))
         0)
       (zyp-inserted-length (cdr patch)))))

(defun zyp-output-length (patch)
  (+ (zyp-kept-length patch)
     (zyp-inserted-length patch)))

(defthm zyp-source-demand-of-append
  (equal (zyp-source-demand (append left right))
         (+ (zyp-source-demand left)
            (zyp-source-demand right))))

(defthm zyp-kept-length-of-append
  (equal (zyp-kept-length (append left right))
         (+ (zyp-kept-length left)
            (zyp-kept-length right))))

(defthm zyp-inserted-length-of-append
  (equal (zyp-inserted-length (append left right))
         (+ (zyp-inserted-length left)
            (zyp-inserted-length right))))

(defthm zyp-output-length-of-append
  (equal (zyp-output-length (append left right))
         (+ (zyp-output-length left)
            (zyp-output-length right))))

(defthm zyp-len-of-patch-output-when-okp
  (implies (zyp-patch-okp patch source)
           (equal (len (zyp-patch-output patch source))
                  (zyp-output-length patch)))
  :hints
  (("Goal"
    :induct (zyp-patch-output patch source)
    :in-theory
    (enable zyp-patch-output
            zyp-patch-okp
            zyp-output-length
            zyp-kept-length
            zyp-inserted-length
            zyp-step-output
            zyp-step-rest
            zyp-step-okp))))

(defthm zyp-len-of-patch-rest-when-okp
  (implies (zyp-patch-okp patch source)
           (equal (len (zyp-patch-rest patch source))
                  (- (len source)
                     (zyp-source-demand patch))))
  :hints
  (("Goal"
    :induct (zyp-patch-rest patch source)
    :in-theory
    (enable zyp-patch-rest
            zyp-patch-okp
            zyp-source-demand
            zyp-step-rest
            zyp-step-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Canonical patch construction
;;
;; ZYP-EMIT is the one smart constructor used by normalization.  It removes
;; empty operations and malformed instructions, merges adjacent KEEP/DROP
;; instructions, and joins adjacent INSERT instructions through ZZE's
;; canonical RLE join.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-emit (instruction patch)
  (cond
   ((zyp-keep-p instruction)
    (let ((count (zyp-count instruction)))
      (cond ((zp count)
             patch)
            ((and (consp patch)
                  (zyp-keep-p (car patch)))
             (cons (zyp-keep
                    (+ count
                       (zyp-count (car patch))))
                   (cdr patch)))
            (t
             (cons (zyp-keep count) patch)))))
   ((zyp-drop-p instruction)
    (let ((count (zyp-count instruction)))
      (cond ((zp count)
             patch)
            ((and (consp patch)
                  (zyp-drop-p (car patch)))
             (cons (zyp-drop
                    (+ count
                       (zyp-count (car patch))))
                   (cdr patch)))
            (t
             (cons (zyp-drop count) patch)))))
   ((zyp-insert-p instruction)
    (let ((runs (xef-rle-canonicalize
                 (zyp-insert-runs instruction))))
      (cond ((endp runs)
             patch)
            ((and (consp patch)
                  (zyp-insert-p (car patch)))
             (cons (zyp-insert
                    (xef-rle-join
                     runs
                     (zyp-insert-runs (car patch))))
                   (cdr patch)))
            (t
             (cons (zyp-insert runs) patch)))))
   (t
    patch)))

(defun zyp-canonical-p (patch)
  (if (endp patch)
      t
    (and
     (cond
      ((zyp-keep-p (car patch))
       (and (posp (zyp-count (car patch)))
            (or (endp (cdr patch))
                (not (zyp-keep-p (cadr patch))))))
      ((zyp-drop-p (car patch))
       (and (posp (zyp-count (car patch)))
            (or (endp (cdr patch))
                (not (zyp-drop-p (cadr patch))))))
      ((zyp-insert-p (car patch))
       (and (consp (zyp-insert-runs (car patch)))
            (xef-rle-canonical-p
             (zyp-insert-runs (car patch)))
            (or (endp (cdr patch))
                (not (zyp-insert-p (cadr patch))))))
      (t nil))
     (zyp-canonical-p (cdr patch)))))

(defun zyp-normalize (patch)
  (if (endp patch)
      nil
    (zyp-emit (car patch)
              (zyp-normalize (cdr patch)))))

; Canonical RLE data cannot disappear when canonicalization sees a positive
; first run.  These are representation-interface facts needed when two INSERT
; instructions are fused: the joined payload remains observably nonempty, even
; though XEF-RLE-JOIN and ZYP-INSERT each normalize their input.
(defthm zyp-rle-canonicalize-consp-when-first-count-positive
  (implies (and (consp runs)
                (posp (cdar runs)))
           (consp (xef-rle-canonicalize runs)))
  :hints
  (("Goal"
    :expand ((xef-rle-canonicalize runs))
    :in-theory (enable xef-rle-emit))))

(defthm zyp-rle-canonicalize-consp-when-canonical
  (implies (and (consp runs)
                (xef-rle-canonical-p runs))
           (consp (xef-rle-canonicalize runs)))
  :hints
  (("Goal"
    :use ((:instance
           zyp-rle-canonicalize-consp-when-first-count-positive
           (runs runs)))
    :in-theory (enable xef-rle-canonical-p))))

(defthm zyp-rle-canonicalize-of-append-consp
  (implies (and (consp left)
                (xef-rle-canonical-p left))
           (consp
            (xef-rle-canonicalize (append left right))))
  :hints
  (("Goal"
    :use ((:instance
           zyp-rle-canonicalize-consp-when-first-count-positive
           (runs (append left right))))
    :in-theory (enable xef-rle-canonical-p))))

(defthm zyp-rle-double-canonicalize-of-append-consp
  (implies (and (consp left)
                (xef-rle-canonical-p left))
           (consp
            (xef-rle-canonicalize
             (xef-rle-canonicalize
              (append left right)))))
  :hints
  (("Goal"
    :use ((:instance
           zyp-rle-canonicalize-of-append-consp
           (left left)
           (right right))
          (:instance
           zyp-rle-canonicalize-consp-when-canonical
           (runs (xef-rle-canonicalize
                  (append left right))))))))

(defthm zyp-canonical-p-of-emit
  (implies (zyp-canonical-p patch)
           (zyp-canonical-p
            (zyp-emit instruction patch)))
  :hints
  (("Goal"
    :use ((:instance
           zyp-rle-double-canonicalize-of-append-consp
           (left (xef-rle-canonicalize
                  (zyp-insert-runs instruction)))
           (right (zyp-insert-runs (car patch)))))
    :in-theory
    (enable zyp-emit
            zyp-canonical-p
            zyp-keep
            zyp-drop
            zyp-insert))))

(defthm zyp-canonical-p-of-normalize
  (zyp-canonical-p (zyp-normalize patch))
  :hints
  (("Goal"
    :induct (zyp-normalize patch)
    :in-theory (enable zyp-normalize))))

; These one-step semantic interfaces expose exactly one patch instruction
; without enabling the recursive projection definitions globally.  They are
; especially useful for smart-constructor proofs: ACL2 may inspect the head of
; an emitted patch while the recursive tail remains abstract.
(defthm zyp-patch-rest-open-when-consp
  (implies (consp patch)
           (equal (zyp-patch-rest patch source)
                  (zyp-patch-rest
                   (cdr patch)
                   (zyp-step-rest (car patch) source))))
  :hints
  (("Goal"
    :expand ((zyp-patch-rest patch source)))))

(defthm zyp-patch-output-open-when-consp
  (implies (consp patch)
           (equal (zyp-patch-output patch source)
                  (append
                   (zyp-step-output (car patch) source)
                   (zyp-patch-output
                    (cdr patch)
                    (zyp-step-rest (car patch) source)))))
  :hints
  (("Goal"
    :expand ((zyp-patch-output patch source)))))

(defthm zyp-patch-okp-open-when-consp
  (implies (consp patch)
           (equal (zyp-patch-okp patch source)
                  (and
                   (zyp-step-okp (car patch) source)
                   (zyp-patch-okp
                    (cdr patch)
                    (zyp-step-rest (car patch) source)))))
  :hints
  (("Goal"
    :expand ((zyp-patch-okp patch source)))))

; Fusing adjacent KEEP or DROP instructions is sequential source
; consumption.  The three projection laws below isolate that algebra from the
; case analysis in ZYP-EMIT.  They are intentionally semantic: later proofs do
; not need to reopen the recursive prefix functions.
(defthm zyp-patch-rest-of-fused-consumption
  (equal
   (zyp-patch-rest
    patch
    (zyp-drop-prefix (+ (nfix m) (nfix n)) source))
   (zyp-patch-rest
    patch
    (zyp-drop-prefix n
                     (zyp-drop-prefix m source))))
  :hints
  (("Goal"
    :use ((:instance zyp-drop-prefix-of-sum
                     (m m)
                     (n n)
                     (xs source))))))

(defthm zyp-patch-output-of-fused-consumption
  (equal
   (zyp-patch-output
    patch
    (zyp-drop-prefix (+ (nfix m) (nfix n)) source))
   (zyp-patch-output
    patch
    (zyp-drop-prefix n
                     (zyp-drop-prefix m source))))
  :hints
  (("Goal"
    :use ((:instance zyp-drop-prefix-of-sum
                     (m m)
                     (n n)
                     (xs source)))
    :in-theory (disable zyp-drop-prefix-of-sum))))

(defthm zyp-patch-output-of-fused-keeps
  (equal
   (append
    (zyp-take (+ (nfix m) (nfix n)) source)
    (zyp-patch-output
     patch
     (zyp-drop-prefix (+ (nfix m) (nfix n)) source)))
   (append
    (zyp-take m source)
    (append
     (zyp-take n (zyp-drop-prefix m source))
     (zyp-patch-output
      patch
      (zyp-drop-prefix n
                       (zyp-drop-prefix m source))))))
  :hints
  (("Goal"
    :use ((:instance zyp-take-of-sum
                     (m m)
                     (n n)
                     (xs source))
          (:instance zyp-drop-prefix-of-sum
                     (m m)
                     (n n)
                     (xs source)))
    :in-theory (enable associativity-of-append))))

(defthm zyp-patch-okp-of-fused-consumption
  (equal
   (and
    (zyp-enoughp (+ (nfix m) (nfix n)) source)
    (zyp-patch-okp
     patch
     (zyp-drop-prefix (+ (nfix m) (nfix n)) source)))
   (and
    (zyp-enoughp m source)
    (zyp-enoughp n (zyp-drop-prefix m source))
    (zyp-patch-okp
     patch
     (zyp-drop-prefix n
                      (zyp-drop-prefix m source)))))
  :hints
  (("Goal"
    :use ((:instance zyp-enoughp-of-sum
                     (m m)
                     (n n)
                     (xs source))
          (:instance zyp-drop-prefix-of-sum
                     (m m)
                     (n n)
                     (xs source))))))

; One emitted instruction has the same three observations as placing that
; instruction literally in front of the already-normalized tail.
(defthm zyp-patch-rest-of-emit
  (equal (zyp-patch-rest
          (zyp-emit instruction patch)
          source)
         (zyp-patch-rest
          (cons instruction patch)
          source))
  :hints
  (("Goal"
    :use ((:instance zyp-patch-rest-of-fused-consumption
                     (m (zyp-count instruction))
                     (n (zyp-count (car patch)))
                     (patch (cdr patch))
                     (source source)))
    :in-theory
    (e/d (zyp-emit
          zyp-patch-rest-open-when-consp
          zyp-step-rest
          zyp-keep
          zyp-drop
          zyp-insert)
         (zyp-patch-rest
          zyp-patch-rest-of-fused-consumption
          zyp-drop-prefix-of-sum)))))

; If normalization removes an INSERT payload entirely, the original payload
; decoded to the empty word.  This is the semantic bridge between the
; representation test in ZYP-EMIT and the observable output projection.
(defthm zyp-rle-decode-when-canonicalize-not-consp
  (implies (not (consp (xef-rle-canonicalize runs)))
           (equal (xef-rle-decode runs) nil))
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-canonicalize
                     (runs runs)))
    :in-theory (disable xef-rle-decode-of-canonicalize))))

(defthm zyp-patch-output-of-emit
  (equal (zyp-patch-output
          (zyp-emit instruction patch)
          source)
         (zyp-patch-output
          (cons instruction patch)
          source))
  :hints
  (("Goal"
    :use ((:instance zyp-patch-output-of-fused-consumption
                     (m (zyp-count instruction))
                     (n (zyp-count (car patch)))
                     (patch (cdr patch))
                     (source source))
          (:instance zyp-patch-output-of-fused-keeps
                     (m (zyp-count instruction))
                     (n (zyp-count (car patch)))
                     (patch (cdr patch))
                     (source source))
          (:instance xef-rle-decode-of-join
                     (left (xef-rle-canonicalize
                            (zyp-insert-runs instruction)))
                     (right (zyp-insert-runs (car patch))))
          (:instance zyp-rle-decode-when-canonicalize-not-consp
                     (runs (zyp-insert-runs instruction))))
    :in-theory
    (e/d (zyp-emit
          zyp-patch-output-open-when-consp
          zyp-patch-rest-open-when-consp
          zyp-step-output
          zyp-step-rest
          zyp-keep
          zyp-drop
          zyp-insert)
         (zyp-patch-output
          zyp-patch-rest
          zyp-patch-output-of-fused-consumption
          zyp-drop-prefix-of-sum)))))

(defthm zyp-patch-okp-of-emit
  (equal (zyp-patch-okp
          (zyp-emit instruction patch)
          source)
         (zyp-patch-okp
          (cons instruction patch)
          source))
  :hints
  (("Goal"
    :use ((:instance zyp-patch-okp-of-fused-consumption
                     (m (zyp-count instruction))
                     (n (zyp-count (car patch)))
                     (patch (cdr patch))
                     (source source)))
    :in-theory
    (e/d (zyp-emit
          zyp-patch-okp-open-when-consp
          zyp-patch-rest-open-when-consp
          zyp-step-okp
          zyp-step-rest
          zyp-keep
          zyp-drop
          zyp-insert)
         (zyp-patch-okp
          zyp-patch-rest
          zyp-patch-okp-of-fused-consumption
          zyp-drop-prefix-of-sum)))))

(defthm zyp-patch-rest-of-normalize
  (equal (zyp-patch-rest (zyp-normalize patch) source)
         (zyp-patch-rest patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-rest patch source)
    :in-theory
    (e/d (zyp-normalize
          zyp-patch-rest)
         (zyp-emit
          zyp-patch-rest-open-when-consp)))))

(defthm zyp-patch-output-of-normalize
  (equal (zyp-patch-output (zyp-normalize patch) source)
         (zyp-patch-output patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-output patch source)
    :in-theory
    (e/d (zyp-normalize
          zyp-patch-output
          zyp-patch-rest)
         (zyp-emit
          zyp-patch-output-open-when-consp
          zyp-patch-rest-open-when-consp)))))

(defthm zyp-patch-okp-of-normalize
  (equal (zyp-patch-okp (zyp-normalize patch) source)
         (zyp-patch-okp patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-okp patch source)
    :in-theory
    (e/d (zyp-normalize
          zyp-patch-okp
          zyp-patch-rest)
         (zyp-emit
          zyp-patch-okp-open-when-consp
          zyp-patch-rest-open-when-consp)))))

(defthm zyp-apply-of-normalize
  (equal (zyp-apply (zyp-normalize patch) source)
         (zyp-apply patch source))
  :hints
  (("Goal"
    :in-theory (enable zyp-apply))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Direct semantic compilation
;;
;; KEEP contributes the summary of the retained prefix, DROP contributes the
;; identity, and INSERT contributes XEF-RLE-SUMMARY directly.  The patch
;; summary therefore avoids materializing inserted words or the final output.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zyp-step-summary (instruction source table)
  (cond ((zyp-keep-p instruction)
         (xef-word-summary
          (zyp-take (zyp-count instruction) source)
          table))
        ((zyp-insert-p instruction)
         (xef-rle-summary
          (zyp-insert-runs instruction)
          table))
        (t
         (xef-cocycle-id))))

(defun zyp-patch-summary (patch source table)
  (if (endp patch)
      (xef-cocycle-id)
    (xef-cocycle-compose
     (zyp-patch-summary
      (cdr patch)
      (zyp-step-rest (car patch) source)
      table)
     (zyp-step-summary (car patch) source table))))

(defun zyp-patch-run (patch source initial-state table)
  (xef-cocycle-eval
   (zyp-patch-summary patch source table)
   initial-state))

(defthm zyp-step-summary-refines-output
  (equal (zyp-step-summary instruction source table)
         (xef-word-summary
          (zyp-step-output instruction source)
          table))
  :hints
  (("Goal"
    :in-theory
    (enable zyp-step-summary
            zyp-step-output))))

; PATCH-SUMMARY is always a canonical cocycle: the empty patch yields the
; canonical identity and every nonempty patch is built by COMPOSE, whose result
; is fixed.  This keeps monoid identity reasoning above the four coordinates.
(defthm zyp-cocycle-fix-of-patch-summary
  (equal (xef-cocycle-fix
          (zyp-patch-summary patch source table))
         (zyp-patch-summary patch source table))
  :hints
  (("Goal"
    :induct (zyp-patch-summary patch source table)
    :in-theory
    (e/d (zyp-patch-summary)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

(defthm zyp-patch-summary-refines-output
  (equal (zyp-patch-summary patch source table)
         (xef-word-summary
          (zyp-patch-output patch source)
          table))
  :hints
  (("Goal"
    :induct (zyp-patch-summary patch source table)
    :in-theory
    (e/d (zyp-patch-summary
          zyp-patch-output)
         (zyp-step-summary
          zyp-step-output
          zyp-step-rest
          xef-word-summary
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

(defthm zyp-patch-run-refines-output
  (equal (zyp-patch-run patch source initial-state table)
         (xef-word-run
          (zyp-patch-output patch source)
          initial-state
          table))
  :hints
  (("Goal"
    :in-theory (enable zyp-patch-run))))

(defthm zyp-patch-summary-of-normalize
  (equal (zyp-patch-summary
          (zyp-normalize patch)
          source
          table)
         (zyp-patch-summary patch source table)))

(defthm zyp-patch-run-of-normalize
  (equal (zyp-patch-run
          (zyp-normalize patch)
          source
          initial-state
          table)
         (zyp-patch-run
          patch
          source
          initial-state
          table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 8. Small recognizable examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zyp-demo-source*
  '(a b c d e f))

(defconst *zyp-demo-patch*
  (list (zyp-keep 2)
        (zyp-drop 2)
        (zyp-insert (xef-rle-encode '(x x y)))
        (zyp-keep 2)))

(assert-event
 (equal (zyp-apply *zyp-demo-patch* *zyp-demo-source*)
        (zyp-result t '(a b x x y e f) nil)))

(assert-event
 (equal (zyp-source-demand *zyp-demo-patch*) 6))

(assert-event
 (equal (zyp-output-length *zyp-demo-patch*) 7))

; Normalization removes empty operations and fuses each adjacent family.
(defconst *zyp-untidy-patch*
  (list (zyp-keep 0)
        (zyp-keep 1)
        (zyp-keep 2)
        (zyp-drop 1)
        (zyp-drop 2)
        (zyp-insert (xef-rle-encode '(u u)))
        (zyp-insert (xef-rle-encode '(u v)))))

(assert-event
 (equal (zyp-normalize *zyp-untidy-patch*)
        (list (zyp-keep 3)
              (zyp-drop 3)
              (zyp-insert (xef-rle-encode '(u u u v))))))

(assert-event
 (equal (zyp-apply
         (zyp-normalize *zyp-untidy-patch*)
         '(a b c d e f))
        (zyp-apply
         *zyp-untidy-patch*
         '(a b c d e f))))

; A familiar command table from ZZE: move on a number line and count steps.
(defconst *zyp-walk-table*
  (list (cons 'right (xef-cocycle 1 1 0 1))
        (cons 'left  (xef-cocycle 1 -1 0 1))))

(defconst *zyp-walk-patch*
  (list (zyp-keep 2)
        (zyp-drop 1)
        (zyp-insert
         (xef-rle-canonicalize
          '((right . 3) (left . 1))))
        (zyp-keep 1)))

(assert-event
 (equal (zyp-patch-output
         *zyp-walk-patch*
         '(right left left right))
        '(right left right right right left right)))

(assert-event
 (equal (zyp-patch-run
         *zyp-walk-patch*
         '(right left left right)
         0
         *zyp-walk-table*)
        '(3 . 7)))

(defxdoc zyp-user-interface
  :parents (zyl-verified-patch-calculus)
  :short "The patch operations intended for ordinary client books."
  :long
  "<p>Construct instructions with <tt>ZYP-KEEP</tt>,
  <tt>ZYP-DROP</tt>, and <tt>ZYP-INSERT</tt>.  Apply a patch with
  <tt>ZYP-APPLY</tt>, or inspect its projections with
  <tt>ZYP-PATCH-OKP</tt>, <tt>ZYP-PATCH-OUTPUT</tt>, and
  <tt>ZYP-PATCH-REST</tt>.</p>

  <p><tt>ZYP-NORMALIZE</tt> selects a canonical edit-script representation.
  <tt>ZYP-SOURCE-DEMAND</tt> and <tt>ZYP-OUTPUT-LENGTH</tt> provide static size
  information.  When only downstream affine semantics matter,
  <tt>ZYP-PATCH-SUMMARY</tt> and <tt>ZYP-PATCH-RUN</tt> bypass construction of
  the complete output word.</p>

  <p>The next dependent layer is intended to add patch composition and
  rope-local application.  Those operations are deliberately absent here so
  that the elementary patch semantics and normalization laws can receive an
  independent ACL2 certification verdict first.</p>")
