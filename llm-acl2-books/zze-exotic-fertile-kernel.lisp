; zzh-exotic-fertile-kernel.lisp
;
; A self-contained ACL2 research kernel for:
;   * affine state transformations carrying additive linear cocycles,
;   * finite-word summaries and run-length acceleration,
;   * bidirectional summaries, binary ropes, and zipper contexts,
;   * change of coordinates, reversible actions, and coboundaries.
;
; This file intentionally contains no skip-proofs, defaxiom, trust tags,
; program-mode definitions, raw Lisp, or generated events.  Every theorem is
; presented to ACL2 as an ordinary proof obligation.
; This is intended to be a conventional ACL2 book: certify it, then bring it
; into other developments with INCLUDE-BOOK.  Ground examples are retained as
; ASSERT-EVENT checks, while reusable claims are ordinary DEFTHM events.
;
; Provenance:
;   Sections 0--11 preserve the logical contents of ZZJ, which completed
;   successfully in the user's ACL2 session.  ZZI extended the RLE interface;
;   ACL2 admitted its canonicalizer results and first stopped at the encoder
;   round-trip theorem.  This revision replaces that proof by a layered API.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc xef-exotic-fertile-kernel
  :parents (acl2::top)
  :short "Affine cocycles, compressed action programs, ropes, zippers, and reversible execution."
  :long
  "<p>This book develops affine state transformations carrying additive linear
  observations.  Finite words and run-length encoded words compile to exact
  cocycle summaries; bidirectional summaries support ropes and zipper contexts;
  later sections add coordinate transport, linear potentials, and reversible
  execution.</p>

  <p>The intended public interface uses the <tt>XEF-COCYCLE</tt> constructor,
  its named accessors, evaluation and summary functions, and the RLE toolkit.
  Clients should not depend on the nested-cons representation of cocycles.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0. Small total list utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-repeat (n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons x (xef-repeat (1- n) x))))

(defun xef-rev (xs)
  (if (endp xs)
      nil
    (append (xef-rev (cdr xs))
            (list (car xs)))))

(defthm xef-len-of-repeat
  (equal (len (xef-repeat n x))
         (nfix n)))

(defthm xef-rev-of-append
  (equal (xef-rev (append xs ys))
         (append (xef-rev ys)
                 (xef-rev xs)))
  :hints (("Goal" :induct (xef-rev xs))))

(defthm xef-rev-of-rev
  (equal (xef-rev (xef-rev xs))
         (true-list-fix xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Affine cocycles
;;
;; A cocycle C is represented by four integers (a,b,p,q).  Acting on a state x
;; gives
;;
;;       x'    = a*x + b
;;       cost  = p*x + q.
;;
;; Costs add when actions are placed in sequence.  Thus these objects form a
;; semidirect-product monoid: an affine action together with a linear additive
;; observable.  The observable is deliberately retained, since it turns a
;; mere state transformer into a device for exact path statistics.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-cocycle (a b p q)
  (cons (cons (ifix a) (ifix b))
        (cons (ifix p) (ifix q))))

(defun xef-cocycle-a (c)
  (ifix (caar c)))

(defun xef-cocycle-b (c)
  (ifix (cdar c)))

(defun xef-cocycle-p (c)
  (ifix (cadr c)))

(defun xef-cocycle-q (c)
  (ifix (cddr c)))

(defun xef-cocycle-fix (c)
  (xef-cocycle (xef-cocycle-a c)
               (xef-cocycle-b c)
               (xef-cocycle-p c)
               (xef-cocycle-q c)))

(defun xef-cocycle-id ()
  (xef-cocycle 1 0 0 0))

(defun xef-cocycle-eval (c x)
  (let ((x (ifix x)))
    (cons (+ (* (xef-cocycle-a c) x)
             (xef-cocycle-b c))
          (+ (* (xef-cocycle-p c) x)
             (xef-cocycle-q c)))))

; Evaluation always returns an integer state paired with an integer cost.
; These type-prescription rules are part of the semantic interface of
; cocycles.  In particular, they prevent later transport proofs from splitting
; on impossible non-integer branches created by IFIX.
(defthm xef-integerp-of-cocycle-eval-state
  (integerp (car (xef-cocycle-eval c x)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory
    (enable xef-cocycle-eval
            xef-cocycle-a
            xef-cocycle-b))))

(defthm xef-integerp-of-cocycle-eval-cost
  (integerp (cdr (xef-cocycle-eval c x)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory
    (enable xef-cocycle-eval
            xef-cocycle-p
            xef-cocycle-q))))

; IFIX is intentionally kept opaque in many algebraic proofs below.
; This interface lemma permits normalization whenever ACL2 can establish
; integer-valuedness, without opening IFIX into irrelevant case splits.
(defthm xef-ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x))
  :hints (("Goal" :in-theory (enable ifix))))

; XEF-COCYCLE-COMPOSE places EARLIER first and LATER second.
(defun xef-cocycle-compose (later earlier)
  (xef-cocycle
   (* (xef-cocycle-a later)
      (xef-cocycle-a earlier))
   (+ (* (xef-cocycle-a later)
         (xef-cocycle-b earlier))
      (xef-cocycle-b later))
   (+ (xef-cocycle-p earlier)
      (* (xef-cocycle-p later)
         (xef-cocycle-a earlier)))
   (+ (xef-cocycle-q earlier)
      (* (xef-cocycle-p later)
         (xef-cocycle-b earlier))
      (xef-cocycle-q later))))

(defun xef-chain-results (first second)
  (cons (car second)
        (+ (ifix (cdr first))
           (ifix (cdr second)))))

; These are the abstract laws needed later.  Keeping them visible lets ACL2
; reason about sequential observations without repeatedly opening the four
; integer coordinates of a cocycle.
(defthm xef-car-of-chain-results
  (equal (car (xef-chain-results first second))
         (car second)))

(defthm xef-cdr-of-chain-results
  (equal (cdr (xef-chain-results first second))
         (+ (ifix (cdr first))
            (ifix (cdr second)))))

(defthm xef-chain-results-associative
  (equal (xef-chain-results
          (xef-chain-results first second)
          third)
         (xef-chain-results
          first
          (xef-chain-results second third))))

(defthm xef-cocycle-fix-idempotent
  (equal (xef-cocycle-fix (xef-cocycle-fix c))
         (xef-cocycle-fix c)))

(defthm xef-cocycle-a-of-fix
  (equal (xef-cocycle-a (xef-cocycle-fix c))
         (xef-cocycle-a c)))

(defthm xef-cocycle-b-of-fix
  (equal (xef-cocycle-b (xef-cocycle-fix c))
         (xef-cocycle-b c)))

(defthm xef-cocycle-p-of-fix
  (equal (xef-cocycle-p (xef-cocycle-fix c))
         (xef-cocycle-p c)))

(defthm xef-cocycle-q-of-fix
  (equal (xef-cocycle-q (xef-cocycle-fix c))
         (xef-cocycle-q c)))

(defthm xef-cocycle-eval-of-fix
  (equal (xef-cocycle-eval (xef-cocycle-fix c) x)
         (xef-cocycle-eval c x)))

(defthm xef-cocycle-fix-of-compose
  (equal (xef-cocycle-fix
          (xef-cocycle-compose later earlier))
         (xef-cocycle-compose later earlier)))

(defthm xef-cocycle-eval-of-id
  (equal (xef-cocycle-eval (xef-cocycle-id) x)
         (cons (ifix x) 0)))

(defthm xef-cocycle-compose-left-identity
  (equal (xef-cocycle-compose (xef-cocycle-id) c)
         (xef-cocycle-fix c)))

(defthm xef-cocycle-compose-right-identity
  (equal (xef-cocycle-compose c (xef-cocycle-id))
         (xef-cocycle-fix c)))

(defthm xef-cocycle-eval-of-compose
  (equal (xef-cocycle-eval
          (xef-cocycle-compose later earlier)
          x)
         (let* ((first  (xef-cocycle-eval earlier x))
                (second (xef-cocycle-eval later (car first))))
           (xef-chain-results first second))))

; Two probes determine all four integer parameters: x=0 reveals b and q,
; while x=1 reveals a+b and p+q.
(defthm xef-cocycle-two-probe-extensionality
  (implies (and (equal (xef-cocycle-eval c 0)
                       (xef-cocycle-eval d 0))
                (equal (xef-cocycle-eval c 1)
                       (xef-cocycle-eval d 1)))
           (equal (xef-cocycle-fix c)
                  (xef-cocycle-fix d))))

; Associativity is now proved extensionally.  The evaluation law and the
; associativity of XEF-CHAIN-RESULTS do the semantic work; the two probes turn
; that semantic equality back into equality of canonical cocycles.  Disabling
; the low-level definitions prevents an exponential spray of IFIX cases.
(defthm xef-cocycle-compose-associative
  (equal (xef-cocycle-compose
          third
          (xef-cocycle-compose second first))
         (xef-cocycle-compose
          (xef-cocycle-compose third second)
          first))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-cocycle-two-probe-extensionality
      (c (xef-cocycle-compose
          third
          (xef-cocycle-compose second first)))
      (d (xef-cocycle-compose
          (xef-cocycle-compose third second)
          first))))
    :in-theory
    (e/d ()
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-eval
          xef-cocycle-compose
          xef-chain-results)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Powers and exact orbit accumulation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-cocycle-power (n c)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (xef-cocycle-id)
    (xef-cocycle-compose
     (xef-cocycle-power (1- n) c)
     c)))

(defun xef-cocycle-iterate (n c x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons (ifix x) 0)
    (let* ((first (xef-cocycle-eval c x))
           (rest  (xef-cocycle-iterate (1- n) c (car first))))
      (xef-chain-results first rest))))

(defun xef-orbit-states (n c x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list (ifix x))
    (cons (ifix x)
          (xef-orbit-states
           (1- n)
           c
           (car (xef-cocycle-eval c x))))))

(defthm xef-cocycle-power-zero
  (equal (xef-cocycle-power 0 c)
         (xef-cocycle-id)))

(defthm xef-cocycle-power-successor
  (implies (natp n)
           (equal (xef-cocycle-power (+ 1 n) c)
                  (xef-cocycle-compose
                   (xef-cocycle-power n c)
                   c))))

; POWER and ITERATE make exactly the same ZP distinction, and EVAL performs
; the same IFIX totalization as ITERATE's base case.  Hence the semantic law is
; true without type hypotheses.  More importantly, the proof below keeps EVAL
; and COMPOSE abstract, forcing ACL2 to use XEF-COCYCLE-EVAL-OF-COMPOSE instead
; of expanding four coordinates and splitting on malformed cons structures.
(defthm xef-cocycle-iterate-is-power-evaluation
  (equal (xef-cocycle-iterate n c x)
         (xef-cocycle-eval (xef-cocycle-power n c) x))
  :hints
  (("Goal"
    :induct (xef-cocycle-iterate n c x)
    :in-theory
    (e/d (xef-cocycle-iterate
          xef-cocycle-power)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-eval
          xef-cocycle-compose
          xef-chain-results)))))

(defthm xef-len-of-orbit-states
  (equal (len (xef-orbit-states n c x))
         (+ 1 (nfix n))))


; The identity cocycle is already canonical.  This tiny computational lemma
; lets later proofs keep XEF-COCYCLE-FIX and XEF-COCYCLE-ID abstract.
(defthm xef-cocycle-fix-of-id
  (equal (xef-cocycle-fix (xef-cocycle-id))
         (xef-cocycle-id)))

; Every power is canonical for structural reasons: zero is the canonical
; identity, while every positive power is produced by COMPOSE, whose result
; was already proved fixed.  The representation-level definitions are kept
; disabled so ACL2 cannot split on the four IFIX coordinates of C.
(defthm xef-cocycle-fix-of-power
  (equal (xef-cocycle-fix (xef-cocycle-power n c))
         (xef-cocycle-power n c))
  :hints
  (("Goal"
    :induct (xef-cocycle-power n c)
    :in-theory
    (e/d (xef-cocycle-power)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

; Recursion-aligned splitting: POWER adds its newest copy of C as the EARLIER
; action.  Induction on N therefore needs only the monoid laws already proved:
; right identity in the base case, and associativity in the step.  In
; particular, ACL2 is forbidden here from opening the cocycle coordinates.
(defthm xef-cocycle-power-additive
  (implies (and (natp m)
                (natp n))
           (equal (xef-cocycle-power (+ m n) c)
                  (xef-cocycle-compose
                   (xef-cocycle-power m c)
                   (xef-cocycle-power n c))))
  :hints
  (("Goal"
    :induct (xef-cocycle-power n c)
    :in-theory
    (e/d (xef-cocycle-power)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Symbol tables, words, and monoidal summaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-lookup-cocycle (symbol table)
  (if (endp table)
      (xef-cocycle-id)
    (if (equal symbol (caar table))
        (xef-cocycle-fix (cdar table))
      (xef-lookup-cocycle symbol (cdr table)))))

(defthm xef-cocycle-fix-of-lookup
  (equal (xef-cocycle-fix (xef-lookup-cocycle symbol table))
         (xef-lookup-cocycle symbol table))
  :hints
  (("Goal"
    :induct (xef-lookup-cocycle symbol table)
    :in-theory
    (e/d (xef-lookup-cocycle)
         (xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defun xef-word-summary (word table)
  (if (endp word)
      (xef-cocycle-id)
    (xef-cocycle-compose
     (xef-word-summary (cdr word) table)
     (xef-lookup-cocycle (car word) table))))

(defun xef-word-run (word x table)
  (if (endp word)
      (cons (ifix x) 0)
    (let* ((first (xef-cocycle-eval
                   (xef-lookup-cocycle (car word) table)
                   x))
           (rest  (xef-word-run (cdr word) (car first) table)))
      (xef-chain-results first rest))))

(defthm xef-word-summary-of-nil
  (equal (xef-word-summary nil table)
         (xef-cocycle-id))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-word-summary)
         (xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

; WORD-SUMMARY always returns a canonical cocycle.  This structural lemma is
; the missing bridge between the empty-word case and the abstract right-
; identity law.  Keep the representation hidden: the proof needs only that
; ID is canonical and COMPOSE produces a canonical cocycle.
(defthm xef-cocycle-fix-of-word-summary
  (equal (xef-cocycle-fix (xef-word-summary word table))
         (xef-word-summary word table))
  :hints
  (("Goal"
    :induct (xef-word-summary word table)
    :in-theory
    (e/d (xef-word-summary)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

; APPEND recurses on XS, and WORD-SUMMARY consumes a word from its front while
; accumulating the corresponding action on the right.  The proof is thus the
; monoid homomorphism argument: canonical right identity at NIL and
; associativity at CONS.  Coordinate definitions are disabled so ACL2 cannot
; replace that argument by millions of IFIX case splits.
(defthm xef-word-summary-of-append
  (equal (xef-word-summary (append xs ys) table)
         (xef-cocycle-compose
          (xef-word-summary ys table)
          (xef-word-summary xs table)))
  :hints
  (("Goal"
    :induct (xef-word-summary xs table)
    :in-theory
    (e/d (xef-word-summary)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

(defthm xef-word-summary-of-singleton
  (equal (xef-word-summary (list symbol) table)
         (xef-lookup-cocycle symbol table))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-word-summary)
         (xef-lookup-cocycle
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-cocycle-compose)))))

(defthm xef-word-run-is-summary-evaluation
  (equal (xef-word-run word x table)
         (xef-cocycle-eval
          (xef-word-summary word table)
          x))
  :hints
  (("Goal"
    :induct (xef-word-run word x table)
    :in-theory
    (e/d (xef-word-run
          xef-word-summary)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-eval
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-chain-results)))))

(defthm xef-word-run-of-append
  (equal (xef-word-run (append xs ys) x table)
         (let* ((first  (xef-word-run xs x table))
                (second (xef-word-run ys (car first) table)))
           (xef-chain-results first second)))
  :hints
  (("Goal"
    :in-theory
    (e/d ()
         (xef-word-run
          xef-word-summary
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-eval
          xef-cocycle-compose
          xef-chain-results)))))

(defthm xef-word-summary-of-repeat
  (equal (xef-word-summary (xef-repeat n symbol) table)
         (xef-cocycle-power
          n
          (xef-lookup-cocycle symbol table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Run-length words as accelerated action programs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A run is (symbol . count).
(defun xef-rle-decode (runs)
  (if (endp runs)
      nil
    (append (xef-repeat (cdar runs) (caar runs))
            (xef-rle-decode (cdr runs)))))

(defun xef-rle-summary (runs table)
  (if (endp runs)
      (xef-cocycle-id)
    (xef-cocycle-compose
     (xef-rle-summary (cdr runs) table)
     (xef-cocycle-power
      (cdar runs)
      (xef-lookup-cocycle (caar runs) table)))))

(defun xef-rle-run (runs x table)
  (xef-cocycle-eval (xef-rle-summary runs table) x))

(defun xef-rle-symbol-count (runs)
  (if (endp runs)
      0
    (+ (nfix (cdar runs))
       (xef-rle-symbol-count (cdr runs)))))

(defthm xef-len-of-rle-decode
  (equal (len (xef-rle-decode runs))
         (xef-rle-symbol-count runs)))

(defthm xef-rle-summary-refines-decoding
  (equal (xef-rle-summary runs table)
         (xef-word-summary (xef-rle-decode runs) table)))

(defthm xef-rle-run-refines-decoding
  (equal (xef-rle-run runs x table)
         (xef-word-run (xef-rle-decode runs) x table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Bidirectional summaries
;;
;; A bidirectional summary remembers length, forward action, and reverse
;; action.  Joining summaries is constant-time.  This is the algebraic payload
;; later cached by binary ropes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-bi-summary (length forward reverse)
  (list (nfix length)
        (xef-cocycle-fix forward)
        (xef-cocycle-fix reverse)))

(defun xef-bi-length (summary)
  (nfix (car summary)))

(defun xef-bi-forward (summary)
  (xef-cocycle-fix (cadr summary)))

(defun xef-bi-reverse (summary)
  (xef-cocycle-fix (caddr summary)))

(defun xef-bi-empty ()
  (xef-bi-summary 0
                  (xef-cocycle-id)
                  (xef-cocycle-id)))

(defun xef-word-bi-summary (word table)
  (xef-bi-summary
   (len word)
   (xef-word-summary word table)
   (xef-word-summary (xef-rev word) table)))

; LEFT is followed by RIGHT.
(defun xef-bi-join (left right)
  (xef-bi-summary
   (+ (xef-bi-length left)
      (xef-bi-length right))
   (xef-cocycle-compose
    (xef-bi-forward right)
    (xef-bi-forward left))
   (xef-cocycle-compose
    (xef-bi-reverse left)
    (xef-bi-reverse right))))

; These projection laws are the abstraction boundary for bidirectional
; summaries.  They let later proofs reason about the three cached fields
; without reopening the list representation or the four coordinates of a
; cocycle.
(defthm xef-bi-length-of-summary
  (equal (xef-bi-length
          (xef-bi-summary length forward reverse))
         (nfix length))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-bi-summary xef-bi-length)
         (xef-cocycle-fix)))))

(defthm xef-bi-forward-of-summary
  (equal (xef-bi-forward
          (xef-bi-summary length forward reverse))
         (xef-cocycle-fix forward))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-bi-summary xef-bi-forward)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix)))))

(defthm xef-bi-reverse-of-summary
  (equal (xef-bi-reverse
          (xef-bi-summary length forward reverse))
         (xef-cocycle-fix reverse))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-bi-summary xef-bi-reverse)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix)))))

(defthm xef-bi-length-of-join
  (equal (xef-bi-length (xef-bi-join left right))
         (+ (xef-bi-length left)
            (xef-bi-length right)))
  :hints
  (("Goal"
    :expand ((xef-bi-join left right))
    :in-theory
    (disable xef-bi-join
             xef-bi-summary
             xef-bi-length))))

(defthm xef-bi-forward-of-join
  (equal (xef-bi-forward (xef-bi-join left right))
         (xef-cocycle-compose
          (xef-bi-forward right)
          (xef-bi-forward left)))
  :hints
  (("Goal"
    :expand ((xef-bi-join left right))
    :in-theory
    (e/d ()
         (xef-bi-join
          xef-bi-summary
          xef-bi-forward
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-compose)))))

(defthm xef-bi-reverse-of-join
  (equal (xef-bi-reverse (xef-bi-join left right))
         (xef-cocycle-compose
          (xef-bi-reverse left)
          (xef-bi-reverse right)))
  :hints
  (("Goal"
    :expand ((xef-bi-join left right))
    :in-theory
    (e/d ()
         (xef-bi-join
          xef-bi-summary
          xef-bi-reverse
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-compose)))))

(defthm xef-bi-join-left-identity
  (equal (xef-bi-join (xef-bi-empty) summary)
         (xef-bi-summary
          (xef-bi-length summary)
          (xef-bi-forward summary)
          (xef-bi-reverse summary))))

(defthm xef-bi-join-right-identity
  (equal (xef-bi-join summary (xef-bi-empty))
         (xef-bi-summary
          (xef-bi-length summary)
          (xef-bi-forward summary)
          (xef-bi-reverse summary))))

(defthm xef-bi-join-associative
  (equal (xef-bi-join
          (xef-bi-join first second)
          third)
         (xef-bi-join
          first
          (xef-bi-join second third)))
  :hints
  (("Goal"
    :expand
    ((xef-bi-join
      (xef-bi-join first second)
      third)
     (xef-bi-join
      first
      (xef-bi-join second third)))
    :in-theory
    (e/d ()
         (xef-bi-join
          xef-bi-summary
          xef-bi-length
          xef-bi-forward
          xef-bi-reverse
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-compose)))))

(defthm xef-word-bi-summary-of-append
  (equal (xef-word-bi-summary (append xs ys) table)
         (xef-bi-join
          (xef-word-bi-summary xs table)
          (xef-word-bi-summary ys table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Binary ropes with semantic summaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-rope-leaf (word)
  (cons :leaf word))

(defun xef-rope-cat (left right)
  (list :cat left right))

(defun xef-rope-leaf-p (rope)
  (and (consp rope)
       (equal (car rope) :leaf)))

(defun xef-rope-cat-p (rope)
  (and (consp rope)
       (equal (car rope) :cat)))

(defun xef-rope-flatten (rope)
  (cond ((xef-rope-leaf-p rope)
         (true-list-fix (cdr rope)))
        ((xef-rope-cat-p rope)
         (append (xef-rope-flatten (cadr rope))
                 (xef-rope-flatten (caddr rope))))
        (t nil)))

(defun xef-rope-summary (rope table)
  (cond ((xef-rope-leaf-p rope)
         (xef-word-bi-summary (true-list-fix (cdr rope)) table))
        ((xef-rope-cat-p rope)
         (xef-bi-join
          (xef-rope-summary (cadr rope) table)
          (xef-rope-summary (caddr rope) table)))
        (t (xef-bi-empty))))

(defun xef-rope-leaf-count (rope)
  (cond ((xef-rope-leaf-p rope) 1)
        ((xef-rope-cat-p rope)
         (+ (xef-rope-leaf-count (cadr rope))
            (xef-rope-leaf-count (caddr rope))))
        (t 0)))

(defun xef-rope-height (rope)
  (cond ((xef-rope-leaf-p rope) 1)
        ((xef-rope-cat-p rope)
         (+ 1 (max (xef-rope-height (cadr rope))
                   (xef-rope-height (caddr rope)))))
        (t 0)))

(defun xef-rope-forward-run (rope x table)
  (xef-cocycle-eval
   (xef-bi-forward (xef-rope-summary rope table))
   x))

(defun xef-rope-reverse-run (rope x table)
  (xef-cocycle-eval
   (xef-bi-reverse (xef-rope-summary rope table))
   x))

; Constructor laws are deliberately isolated before the global refinement
; theorem.  They keep the recursive proof in the rope algebra and prevent the
; prover from opening the list representation of bidirectional summaries or
; the four integer coordinates of cocycles.
(defthm xef-rope-flatten-of-leaf
  (equal (xef-rope-flatten (xef-rope-leaf word))
         (true-list-fix word))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-leaf
          xef-rope-leaf-p
          xef-rope-cat-p
          xef-rope-flatten)
         ()))))

(defthm xef-rope-flatten-of-cat
  (equal (xef-rope-flatten (xef-rope-cat left right))
         (append (xef-rope-flatten left)
                 (xef-rope-flatten right)))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-cat
          xef-rope-leaf-p
          xef-rope-cat-p
          xef-rope-flatten)
         ()))))

(defthm xef-rope-summary-of-leaf
  (equal (xef-rope-summary (xef-rope-leaf word) table)
         (xef-word-bi-summary (true-list-fix word) table))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-leaf
          xef-rope-leaf-p
          xef-rope-cat-p
          xef-rope-summary)
         (xef-word-bi-summary
          xef-bi-summary
          xef-bi-join)))))

(defthm xef-rope-summary-of-cat
  (equal (xef-rope-summary (xef-rope-cat left right) table)
         (xef-bi-join
          (xef-rope-summary left table)
          (xef-rope-summary right table)))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-cat
          xef-rope-leaf-p
          xef-rope-cat-p
          xef-rope-summary)
         (xef-bi-join)))))

(defthm xef-word-bi-summary-of-nil
  (equal (xef-word-bi-summary nil table)
         (xef-bi-empty))
  :hints
  (("Goal"
    ; Expand exactly the two interface functions whose equality is at issue.
    ; After these expansions, LEN, REV, and WORD-SUMMARY-OF-NIL reduce the
    ; left side to the very same BI-SUMMARY term as the right side.  Keeping
    ; BI-SUMMARY opaque avoids any dependence on its concrete list encoding.
    :expand ((xef-word-bi-summary nil table)
             (xef-bi-empty))
    :in-theory
    (e/d ()
         (xef-word-bi-summary
          (:executable-counterpart xef-word-bi-summary)
          xef-bi-empty
          (:executable-counterpart xef-bi-empty)
          xef-bi-summary
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

; These projection laws turn the full bidirectional summary into a reusable
; interface.  Later execution theorems need not unfold XEF-WORD-BI-SUMMARY.
(defthm xef-bi-length-of-word-bi-summary
  (equal (xef-bi-length (xef-word-bi-summary word table))
         (len word))
  :hints
  (("Goal"
    :expand ((xef-word-bi-summary word table))
    :in-theory
    (e/d ()
         (xef-word-bi-summary
          xef-bi-summary
          xef-bi-length
          xef-word-summary
          xef-rev)))))

(defthm xef-bi-forward-of-word-bi-summary
  (equal (xef-bi-forward (xef-word-bi-summary word table))
         (xef-word-summary word table))
  :hints
  (("Goal"
    :expand ((xef-word-bi-summary word table))
    :in-theory
    (e/d ()
         (xef-word-bi-summary
          xef-bi-summary
          xef-bi-forward
          xef-word-summary
          xef-rev
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix)))))

(defthm xef-bi-reverse-of-word-bi-summary
  (equal (xef-bi-reverse (xef-word-bi-summary word table))
         (xef-word-summary (xef-rev word) table))
  :hints
  (("Goal"
    :expand ((xef-word-bi-summary word table))
    :in-theory
    (e/d ()
         (xef-word-bi-summary
          xef-bi-summary
          xef-bi-reverse
          xef-word-summary
          xef-rev
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix)))))

(defthm xef-rope-summary-refines-flattening
  (equal (xef-rope-summary rope table)
         (xef-word-bi-summary
          (xef-rope-flatten rope)
          table))
  :hints
  (("Goal"
    :induct (xef-rope-summary rope table)
    :in-theory
    (e/d (xef-rope-summary
          xef-rope-flatten)
         (xef-rope-leaf-p
          xef-rope-cat-p
          xef-word-bi-summary
          xef-bi-empty
          (:executable-counterpart xef-bi-empty)
          xef-bi-summary
          xef-bi-join
          xef-bi-length
          xef-bi-forward
          xef-bi-reverse
          xef-word-summary
          xef-rev
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-compose)))))

(defthm xef-bi-length-of-rope-summary
  (equal (xef-bi-length (xef-rope-summary rope table))
         (len (xef-rope-flatten rope)))
  :hints
  (("Goal"
    :in-theory
    (e/d ()
         (xef-rope-summary
          xef-rope-flatten
          xef-word-bi-summary
          xef-bi-length)))))

(defthm xef-bi-forward-of-rope-summary
  (equal (xef-bi-forward (xef-rope-summary rope table))
         (xef-word-summary (xef-rope-flatten rope) table))
  :hints
  (("Goal"
    :in-theory
    (e/d ()
         (xef-rope-summary
          xef-rope-flatten
          xef-word-bi-summary
          xef-bi-forward
          xef-word-summary)))))

(defthm xef-bi-reverse-of-rope-summary
  (equal (xef-bi-reverse (xef-rope-summary rope table))
         (xef-word-summary (xef-rev (xef-rope-flatten rope)) table))
  :hints
  (("Goal"
    :in-theory
    (e/d ()
         (xef-rope-summary
          xef-rope-flatten
          xef-word-bi-summary
          xef-bi-reverse
          xef-word-summary
          xef-rev)))))

(defthm xef-rope-forward-run-refines-flattening
  (equal (xef-rope-forward-run rope x table)
         (xef-word-run (xef-rope-flatten rope) x table))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-forward-run)
         (xef-rope-summary
          xef-rope-flatten
          xef-bi-forward
          xef-word-summary
          xef-word-run
          xef-cocycle-eval)))))

(defthm xef-rope-reverse-run-refines-flattening
  (equal (xef-rope-reverse-run rope x table)
         (xef-word-run (xef-rev (xef-rope-flatten rope))
                       x
                       table))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-rope-reverse-run)
         (xef-rope-summary
          xef-rope-flatten
          xef-bi-reverse
          xef-word-summary
          xef-word-run
          xef-rev
          xef-cocycle-eval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Rope zippers and context actions
;;
;; Contexts are listed from the hole outward.  A frame says either that the
;; hole was the left child and remembers the right sibling, or vice versa.
;; Contexts therefore act on ropes and, separately, on cached summaries.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-left-frame (right-sibling)
  (list :left right-sibling))

(defun xef-right-frame (left-sibling)
  (list :right left-sibling))

(defun xef-plug-rope (focus context)
  (if (endp context)
      focus
    (let ((frame (car context)))
      (if (equal (car frame) :left)
          (xef-plug-rope
           (xef-rope-cat focus (cadr frame))
           (cdr context))
        (xef-plug-rope
         (xef-rope-cat (cadr frame) focus)
         (cdr context))))))

(defun xef-plug-summary (focus-summary context table)
  (if (endp context)
      focus-summary
    (let ((frame (car context)))
      (if (equal (car frame) :left)
          (xef-plug-summary
           (xef-bi-join
            focus-summary
            (xef-rope-summary (cadr frame) table))
           (cdr context)
           table)
        (xef-plug-summary
         (xef-bi-join
          (xef-rope-summary (cadr frame) table)
          focus-summary)
         (cdr context)
         table)))))

(defun xef-plug-word (focus-word context)
  (if (endp context)
      focus-word
    (let ((frame (car context)))
      (if (equal (car frame) :left)
          (xef-plug-word
           (append focus-word
                   (xef-rope-flatten (cadr frame)))
           (cdr context))
        (xef-plug-word
         (append (xef-rope-flatten (cadr frame))
                 focus-word)
         (cdr context))))))

(defun xef-replace-focus (new-focus context)
  (xef-plug-rope new-focus context))

(defthm xef-flatten-of-plug-rope
  (equal (xef-rope-flatten
          (xef-plug-rope focus context))
         (xef-plug-word
          (xef-rope-flatten focus)
          context))
  :hints
  (("Goal"
    :induct (xef-plug-rope focus context)
    :in-theory
    (e/d (xef-plug-rope
          xef-plug-word)
         (xef-rope-cat
          xef-rope-flatten)))))

(defthm xef-summary-of-plug-rope
  (equal (xef-rope-summary
          (xef-plug-rope focus context)
          table)
         (xef-plug-summary
          (xef-rope-summary focus table)
          context
          table))
  :hints
  (("Goal"
    :induct (xef-plug-rope focus context)
    :in-theory
    (e/d (xef-plug-rope
          xef-plug-summary)
         (xef-rope-cat
          xef-rope-summary
          xef-bi-join)))))

; The context action itself respects the semantic word interpretation.  This
; theorem is the algebraic heart of incremental recomputation after an edit.
(defthm xef-plug-summary-refines-plug-word
  (equal (xef-plug-summary
          (xef-word-bi-summary focus-word table)
          context
          table)
         (xef-word-bi-summary
          (xef-plug-word focus-word context)
          table))
  :hints
  (("Goal"
    :induct (xef-plug-word focus-word context)
    :in-theory
    (e/d (xef-plug-word
          xef-plug-summary)
         (xef-word-bi-summary
          xef-rope-summary
          xef-rope-flatten
          xef-bi-join)))))

(defthm xef-plug-rope-of-append-contexts
  (equal (xef-plug-rope focus (append inner outer))
         (xef-plug-rope
          (xef-plug-rope focus inner)
          outer))
  :hints
  (("Goal"
    :induct (xef-plug-rope focus inner)
    :in-theory
    (e/d (xef-plug-rope)
         (xef-rope-cat)))))

(defthm xef-plug-summary-of-append-contexts
  (equal (xef-plug-summary
          focus-summary
          (append inner outer)
          table)
         (xef-plug-summary
          (xef-plug-summary focus-summary inner table)
          outer
          table))
  :hints
  (("Goal"
    :induct (xef-plug-summary focus-summary inner table)
    :in-theory
    (e/d (xef-plug-summary)
         (xef-rope-summary
          xef-bi-join)))))

(defthm xef-summary-after-focus-replacement
  (equal (xef-rope-summary
          (xef-replace-focus new-focus context)
          table)
         (xef-plug-summary
          (xef-rope-summary new-focus table)
          context
          table))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-replace-focus)
         (xef-plug-rope
          xef-plug-summary
          xef-rope-summary)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 8. Change of origin
;;
;; Recenter by k means writing the old state as x = y+k.  The transformed
;; cocycle acts on y while preserving accumulated cost.  This gives a concrete
;; conjugacy operation on the state action and a compatible transport of the
;; observable.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-cocycle-recenter (k c)
  (let ((k (ifix k)))
    (xef-cocycle
     (xef-cocycle-a c)
     (+ (* (xef-cocycle-a c) k)
        (xef-cocycle-b c)
        (- k))
     (xef-cocycle-p c)
     (+ (* (xef-cocycle-p c) k)
        (xef-cocycle-q c)))))

(defun xef-recenter-table (k table)
  (if (endp table)
      nil
    (cons (cons (caar table)
                (xef-cocycle-recenter k (cdar table)))
          (xef-recenter-table k (cdr table)))))

(defthm xef-recenter-of-identity
  (equal (xef-cocycle-recenter k (xef-cocycle-id))
         (xef-cocycle-id))
  :hints
  (("Goal"
    :in-theory
    (enable xef-cocycle-recenter
            xef-cocycle-id
            xef-cocycle
            xef-cocycle-a
            xef-cocycle-b
            xef-cocycle-p
            xef-cocycle-q))))

(defthm xef-eval-of-recenter
  (equal (xef-cocycle-eval
          (xef-cocycle-recenter k c)
          y)
         (let ((old-result
                (xef-cocycle-eval
                 c
                 (+ (ifix y) (ifix k)))))
           (cons (- (car old-result) (ifix k))
                 (cdr old-result))))
  :hints
  (("Goal"
    :in-theory
    (enable xef-cocycle-recenter
            xef-cocycle-eval
            xef-cocycle
            xef-cocycle-a
            xef-cocycle-b
            xef-cocycle-p
            xef-cocycle-q))))

(defthm xef-cocycle-fix-of-recenter
  (equal (xef-cocycle-fix (xef-cocycle-recenter k c))
         (xef-cocycle-recenter k c))
  :hints
  (("Goal"
    :in-theory
    (enable xef-cocycle-recenter
            xef-cocycle-fix
            xef-cocycle
            xef-cocycle-a
            xef-cocycle-b
            xef-cocycle-p
            xef-cocycle-q))))

(defthm xef-cocycle-recenter-of-fix
  (equal (xef-cocycle-recenter k (xef-cocycle-fix c))
         (xef-cocycle-recenter k c))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-cocycle-recenter)
         (xef-cocycle-fix
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)))))

(defthm xef-recenter-preserves-composition
  (equal (xef-cocycle-recenter
          k
          (xef-cocycle-compose later earlier))
         (xef-cocycle-compose
          (xef-cocycle-recenter k later)
          (xef-cocycle-recenter k earlier)))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-cocycle-two-probe-extensionality
      (c (xef-cocycle-recenter
          k
          (xef-cocycle-compose later earlier)))
      (d (xef-cocycle-compose
          (xef-cocycle-recenter k later)
          (xef-cocycle-recenter k earlier)))))
    :in-theory
    (e/d (xef-chain-results)
         (xef-cocycle-two-probe-extensionality
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-eval
          xef-cocycle-compose
          xef-cocycle-recenter)))))

(defthm xef-lookup-in-recentered-table
  (equal (xef-lookup-cocycle
          symbol
          (xef-recenter-table k table))
         (xef-cocycle-recenter
          k
          (xef-lookup-cocycle symbol table)))
  :hints
  (("Goal"
    :induct (xef-recenter-table k table)
    :in-theory
    (e/d (xef-recenter-table
          xef-lookup-cocycle)
         (xef-cocycle-recenter
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-summary-in-recentered-coordinates
  (equal (xef-word-summary
          word
          (xef-recenter-table k table))
         (xef-cocycle-recenter
          k
          (xef-word-summary word table)))
  :hints
  (("Goal"
    :induct (xef-word-summary word table)
    :in-theory
    (e/d (xef-word-summary)
         (xef-recenter-table
          xef-lookup-cocycle
          xef-cocycle-recenter
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-cocycle-power-in-recentered-coordinates
  (equal (xef-cocycle-power
          n
          (xef-cocycle-recenter k c))
         (xef-cocycle-recenter
          k
          (xef-cocycle-power n c)))
  :hints
  (("Goal"
    :induct (xef-cocycle-power n c)
    :in-theory
    (e/d (xef-cocycle-power)
         (xef-cocycle-recenter
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-rle-summary-in-recentered-coordinates
  (equal (xef-rle-summary
          runs
          (xef-recenter-table k table))
         (xef-cocycle-recenter
          k
          (xef-rle-summary runs table)))
  :hints
  (("Goal"
    :induct (xef-rle-summary runs table)
    :in-theory
    (e/d (xef-rle-summary)
         (xef-recenter-table
          xef-lookup-cocycle
          xef-cocycle-power
          xef-cocycle-recenter
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 9. Linear coboundaries and telescoping costs
;;
;; A cocycle has the linear potential t*x when
;;
;;       cost(x) = t*x' - t*x.
;;
;; Such costs telescope over arbitrary words.  This is the elementary
;; one-dimensional shadow of cohomology for dynamical systems, but here it is
;; fully executable: ACL2 can calculate the summary and prove the cancellation.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-linear-coboundary (tau a b)
  (xef-cocycle
   a
   b
   (* (ifix tau) (- (ifix a) 1))
   (* (ifix tau) (ifix b))))

(defun xef-has-linear-potential-p (tau c)
  (and (equal (xef-cocycle-p c)
              (* (ifix tau)
                 (- (xef-cocycle-a c) 1)))
       (equal (xef-cocycle-q c)
              (* (ifix tau)
                 (xef-cocycle-b c)))))

(defun xef-table-has-linear-potential-p (tau table)
  (if (endp table)
      t
    (and (xef-has-linear-potential-p tau (cdar table))
         (xef-table-has-linear-potential-p tau (cdr table)))))

(defthm xef-linear-coboundary-has-its-potential
  (xef-has-linear-potential-p
   tau
   (xef-linear-coboundary tau a b))
  :hints
  (("Goal"
    :use
    ((:instance xef-ifix-when-integerp
       (x (* (ifix b) (ifix tau))))
     (:instance xef-ifix-when-integerp
       (x (+ (- (ifix tau))
             (* (ifix a) (ifix tau))))))
    :in-theory
    (e/d (xef-linear-coboundary
          xef-has-linear-potential-p
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-identity-has-every-linear-potential
  (xef-has-linear-potential-p tau (xef-cocycle-id))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-has-linear-potential-p
          xef-cocycle-id
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-linear-potential-of-cocycle-fix
  (equal (xef-has-linear-potential-p
          tau
          (xef-cocycle-fix c))
         (xef-has-linear-potential-p tau c))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-has-linear-potential-p
          xef-cocycle-fix
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-linear-potential-telescopes-in-one-step
  (implies (xef-has-linear-potential-p tau c)
           (equal (cdr (xef-cocycle-eval c x))
                  (* (ifix tau)
                     (- (car (xef-cocycle-eval c x))
                        (ifix x)))))
  ; TAU occurs only in the hypothesis and right-hand side.  Installing this
  ; as a global rewrite rule therefore creates a free-variable rule that ACL2
  ; can rarely use predictably.  The theorem is an explicit semantic bridge;
  ; downstream events instantiate it with :USE.
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-has-linear-potential-p
          xef-cocycle-eval)
         (xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          ifix)))))

; Two observations recover the linear-potential equations.  At state 0,
; telescoping identifies Q = TAU*B.  At state 1 it identifies
; P+Q = TAU*(A+B-1), and the first observation cancels Q.  This theorem is
; deliberately one-way: it is an introduction rule for the coordinate
; predicate from semantic evidence, with no free variables in a rewrite rule.
(defthm xef-linear-potential-from-two-probes
  (implies
   (and
    (equal (cdr (xef-cocycle-eval c 0))
           (* (ifix tau)
              (- (car (xef-cocycle-eval c 0)) 0)))
    (equal (cdr (xef-cocycle-eval c 1))
           (* (ifix tau)
              (- (car (xef-cocycle-eval c 1)) 1))))
   (xef-has-linear-potential-p tau c))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-has-linear-potential-p
          xef-cocycle-eval)
         (ifix)))))

; Sequential telescoping is the semantic reason that potentials survive
; composition.  The proof uses the one-step laws of the two components and
; the already-established evaluation law for cocycle composition.  It never
; opens the four coordinates of XEF-COCYCLE-COMPOSE.
(defthm xef-linear-potential-telescopes-through-composition
  (implies
   (and (xef-has-linear-potential-p tau later)
        (xef-has-linear-potential-p tau earlier))
   (equal
    (cdr (xef-cocycle-eval
          (xef-cocycle-compose later earlier)
          x))
    (* (ifix tau)
       (- (car (xef-cocycle-eval
                (xef-cocycle-compose later earlier)
                x))
          (ifix x)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      xef-linear-potential-telescopes-in-one-step
      (c earlier)
      (x x))
     (:instance
      xef-linear-potential-telescopes-in-one-step
      (c later)
      (x (car (xef-cocycle-eval earlier x)))))
    :in-theory
    (e/d ()
         (xef-has-linear-potential-p
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q
          xef-cocycle-fix
          xef-cocycle-compose
          xef-cocycle-eval
          xef-chain-results
          ifix)))))

; Closure is now a short consequence of semantic telescoping at the two
; probes.  This is intentionally separated from the preceding arithmetic so
; that downstream inductions can use closure as an abstract monoid law.
(defthm xef-linear-potential-closed-under-composition
  (implies (and (xef-has-linear-potential-p tau later)
                (xef-has-linear-potential-p tau earlier))
           (xef-has-linear-potential-p
            tau
            (xef-cocycle-compose later earlier)))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-linear-potential-from-two-probes
      (c (xef-cocycle-compose later earlier))
      (tau tau))
     (:instance
      xef-linear-potential-telescopes-through-composition
      (x 0))
     (:instance
      xef-linear-potential-telescopes-through-composition
      (x 1)))
    :in-theory
    (e/d ()
         (xef-has-linear-potential-p
          xef-cocycle-compose
          xef-cocycle-eval
          ifix)))))

(defthm xef-lookup-preserves-table-potential
  (implies (xef-table-has-linear-potential-p tau table)
           (xef-has-linear-potential-p
            tau
            (xef-lookup-cocycle symbol table)))
  :hints
  (("Goal"
    :induct (xef-lookup-cocycle symbol table)
    :in-theory
    (e/d (xef-table-has-linear-potential-p
          xef-lookup-cocycle)
         (xef-has-linear-potential-p
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-summary-preserves-table-potential
  (implies (xef-table-has-linear-potential-p tau table)
           (xef-has-linear-potential-p
            tau
            (xef-word-summary word table)))
  :hints
  (("Goal"
    :induct (xef-word-summary word table)
    :in-theory
    (e/d (xef-word-summary)
         (xef-table-has-linear-potential-p
          xef-lookup-cocycle
          xef-has-linear-potential-p
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-cost-telescopes
  (implies (xef-table-has-linear-potential-p tau table)
           (equal (cdr (xef-word-run word x table))
                  (* (ifix tau)
                     (- (car (xef-word-run word x table))
                        (ifix x)))))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-linear-potential-telescopes-in-one-step
      (c (xef-word-summary word table))))
    :in-theory
    (e/d ()
         (xef-word-run
          xef-word-summary
          xef-cocycle-eval
          xef-has-linear-potential-p
          xef-table-has-linear-potential-p)))))

(defthm xef-rle-cost-telescopes
  (implies (xef-table-has-linear-potential-p tau table)
           (equal (cdr (xef-rle-run runs x table))
                  (* (ifix tau)
                     (- (car (xef-rle-run runs x table))
                        (ifix x)))))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-word-cost-telescopes
      (word (xef-rle-decode runs))))
    :in-theory
    (e/d ()
         (xef-rle-run
          xef-rle-decode
          xef-word-run
          xef-table-has-linear-potential-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 10. Unit-slope reversibility
;;
;; Integer affine maps are bijections on the integers when a is +1 or -1.
;; The inverse below also negates the accumulated cost along the reversed step.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-unit-cocycle-p (c)
  (or (equal (xef-cocycle-a c) 1)
      (equal (xef-cocycle-a c) -1)))

(defun xef-unit-cocycle-inverse (c)
  (let ((a (xef-cocycle-a c))
        (b (xef-cocycle-b c))
        (p (xef-cocycle-p c))
        (q (xef-cocycle-q c)))
    (xef-cocycle
     a
     (- (* a b))
     (- (* a p))
     (- (* a b p) q))))

(defun xef-unit-table-p (table)
  (if (endp table)
      t
    (and (xef-unit-cocycle-p (cdar table))
         (xef-unit-table-p (cdr table)))))

(defun xef-invert-table (table)
  (if (endp table)
      nil
    (cons (cons (caar table)
                (xef-unit-cocycle-inverse (cdar table)))
          (xef-invert-table (cdr table)))))

(defthm xef-unit-cocycle-p-of-id
  (xef-unit-cocycle-p (xef-cocycle-id))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-cocycle-id
          xef-cocycle
          xef-cocycle-a)
         (ifix)))))

(defthm xef-unit-cocycle-p-of-fix
  (equal (xef-unit-cocycle-p (xef-cocycle-fix c))
         (xef-unit-cocycle-p c))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-p)
         (xef-cocycle-fix
          xef-cocycle-a)))))

(defthm xef-unit-inverse-of-id
  (equal (xef-unit-cocycle-inverse (xef-cocycle-id))
         (xef-cocycle-id))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-inverse
          xef-cocycle-id
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-unit-inverse-of-fix
  (equal (xef-unit-cocycle-inverse (xef-cocycle-fix c))
         (xef-unit-cocycle-inverse c))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-inverse)
         (xef-cocycle-fix
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)))))

(defthm xef-cocycle-fix-of-unit-inverse
  (equal (xef-cocycle-fix (xef-unit-cocycle-inverse c))
         (xef-unit-cocycle-inverse c))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-inverse
          xef-cocycle-fix
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-unit-inverse-is-unit
  (implies (xef-unit-cocycle-p c)
           (xef-unit-cocycle-p
            (xef-unit-cocycle-inverse c)))
  :hints
  (("Goal"
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle
          xef-cocycle-a)
         (ifix)))))

(defthm xef-unit-cocycle-p-of-compose
  (implies (and (xef-unit-cocycle-p later)
                (xef-unit-cocycle-p earlier))
           (xef-unit-cocycle-p
            (xef-cocycle-compose later earlier)))
  :hints
  (("Goal"
    :cases ((equal (xef-cocycle-a later) 1)
            (equal (xef-cocycle-a earlier) 1))
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-cocycle-compose
          xef-cocycle
          xef-cocycle-a)
         (ifix)))))

(defthm xef-unit-inverse-left
  (implies (xef-unit-cocycle-p c)
           (equal (xef-cocycle-compose
                   (xef-unit-cocycle-inverse c)
                   c)
                  (xef-cocycle-id)))
  :hints
  (("Goal"
    :cases ((equal (xef-cocycle-a c) 1))
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-compose
          xef-cocycle-id
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-unit-inverse-right
  (implies (xef-unit-cocycle-p c)
           (equal (xef-cocycle-compose
                   c
                   (xef-unit-cocycle-inverse c))
                  (xef-cocycle-id)))
  :hints
  (("Goal"
    :cases ((equal (xef-cocycle-a c) 1))
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-compose
          xef-cocycle-id
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-unit-inverse-of-compose
  (implies (and (xef-unit-cocycle-p later)
                (xef-unit-cocycle-p earlier))
           (equal (xef-unit-cocycle-inverse
                   (xef-cocycle-compose later earlier))
                  (xef-cocycle-compose
                   (xef-unit-cocycle-inverse earlier)
                   (xef-unit-cocycle-inverse later))))
  :hints
  (("Goal"
    :cases ((equal (xef-cocycle-a later) 1)
            (equal (xef-cocycle-a earlier) 1))
    :in-theory
    (e/d (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-compose
          xef-cocycle
          xef-cocycle-a
          xef-cocycle-b
          xef-cocycle-p
          xef-cocycle-q)
         (ifix)))))

(defthm xef-lookup-preserves-unit-table
  (implies (xef-unit-table-p table)
           (xef-unit-cocycle-p
            (xef-lookup-cocycle symbol table)))
  :hints
  (("Goal"
    :induct (xef-lookup-cocycle symbol table)
    :in-theory
    (e/d (xef-unit-table-p
          xef-lookup-cocycle)
         (xef-unit-cocycle-p
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-summary-preserves-unit-table
  (implies (xef-unit-table-p table)
           (xef-unit-cocycle-p
            (xef-word-summary word table)))
  :hints
  (("Goal"
    :induct (xef-word-summary word table)
    :in-theory
    (e/d (xef-word-summary)
         (xef-unit-table-p
          xef-unit-cocycle-p
          xef-lookup-cocycle
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-lookup-in-inverted-table
  (implies (xef-unit-table-p table)
           (equal (xef-lookup-cocycle
                   symbol
                   (xef-invert-table table))
                  (xef-unit-cocycle-inverse
                   (xef-lookup-cocycle symbol table))))
  :hints
  (("Goal"
    :induct (xef-invert-table table)
    :in-theory
    (e/d (xef-unit-table-p
          xef-invert-table
          xef-lookup-cocycle)
         (xef-unit-cocycle-inverse
          xef-cocycle-fix
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

; An undo summary is computed directly from the original word.  It is useful
; independently of any concrete reversed list: online clients can accumulate
; a forward summary and its exact inverse without storing the whole program.
(defun xef-word-undo-summary (word table)
  (if (endp word)
      (xef-cocycle-id)
    (xef-cocycle-compose
     (xef-unit-cocycle-inverse
      (xef-lookup-cocycle (car word) table))
     (xef-word-undo-summary (cdr word) table))))

(defthm xef-cocycle-fix-of-word-undo-summary
  (equal (xef-cocycle-fix
          (xef-word-undo-summary word table))
         (xef-word-undo-summary word table))
  :hints
  (("Goal"
    :induct (xef-word-undo-summary word table)
    :in-theory
    (e/d (xef-word-undo-summary)
         (xef-cocycle-fix
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-undo-summary-is-inverse
  (implies (xef-unit-table-p table)
           (equal (xef-word-undo-summary word table)
                  (xef-unit-cocycle-inverse
                   (xef-word-summary word table))))
  :hints
  (("Goal"
    :induct (xef-word-summary word table)
    :in-theory
    (e/d (xef-word-summary
          xef-word-undo-summary)
         (xef-unit-table-p
          xef-unit-cocycle-p
          xef-lookup-cocycle
          xef-unit-cocycle-inverse
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-undo-summary-refines-reversed-program
  (implies (xef-unit-table-p table)
           (equal (xef-word-summary
                   (xef-rev word)
                   (xef-invert-table table))
                  (xef-word-undo-summary word table)))
  :hints
  (("Goal"
    :induct (xef-rev word)
    :in-theory
    (e/d (xef-rev
          xef-word-undo-summary)
         (xef-word-summary
          xef-word-bi-summary
          xef-invert-table
          xef-lookup-cocycle
          xef-unit-cocycle-inverse
          xef-word-undo-summary-is-inverse
          xef-cocycle-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id))))))

(defthm xef-word-summary-of-reversed-inverse-program
  (implies (xef-unit-table-p table)
           (equal (xef-word-summary
                   (xef-rev word)
                   (xef-invert-table table))
                  (xef-unit-cocycle-inverse
                   (xef-word-summary word table))))
  :hints
  (("Goal"
    :in-theory
    (e/d ()
         (xef-word-summary
          xef-word-undo-summary
          xef-rev
          xef-invert-table
          xef-unit-cocycle-inverse)))))

; Cancellation is first stated as equality of complete execution results.
; This is the natural semantic consequence of the already-proved left-inverse
; law.  Keeping this theorem at the pair level lets later clients project the
; restored state and the zero total cost independently.
(defthm xef-eval-of-unit-inverse-left-compose
  (implies
   (xef-unit-cocycle-p c)
   (equal
    (xef-cocycle-eval
     (xef-cocycle-compose
      (xef-unit-cocycle-inverse c)
      c)
     x)
    (cons (ifix x) 0)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance xef-unit-inverse-left (c c)))
    :in-theory
    (e/d ()
         (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-compose
          xef-cocycle-eval
          xef-cocycle-eval-of-compose
          xef-cocycle-id
          (:executable-counterpart xef-cocycle-id)
          xef-unit-inverse-left)))))

(defthm xef-unit-inverse-evaluation-chain-cancels
  (implies
   (xef-unit-cocycle-p c)
   (equal
    (xef-chain-results
     (xef-cocycle-eval c x)
     (xef-cocycle-eval
      (xef-unit-cocycle-inverse c)
      (car (xef-cocycle-eval c x))))
    (cons (ifix x) 0)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      xef-cocycle-eval-of-compose
      (later (xef-unit-cocycle-inverse c))
      (earlier c)
      (x x))
     (:instance
      xef-eval-of-unit-inverse-left-compose
      (c c)
      (x x)))
    :in-theory
    (e/d ()
         (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-eval
          xef-cocycle-compose
          xef-chain-results
          xef-cocycle-eval-of-compose)))))

(defthm xef-unit-inverse-evaluation-restores-state
  (implies
   (xef-unit-cocycle-p c)
   (equal
    (car
     (xef-cocycle-eval
      (xef-unit-cocycle-inverse c)
      (car (xef-cocycle-eval c x))))
    (ifix x)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      xef-unit-inverse-evaluation-chain-cancels
      (c c)
      (x x)))
    :in-theory
    (e/d (xef-chain-results)
         (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-eval)))))

(defthm xef-unit-inverse-evaluation-negates-cost
  (implies
   (xef-unit-cocycle-p c)
   (equal
    (+ (cdr (xef-cocycle-eval c x))
       (cdr
        (xef-cocycle-eval
         (xef-unit-cocycle-inverse c)
         (car (xef-cocycle-eval c x)))))
    0))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      xef-unit-inverse-evaluation-chain-cancels
      (c c)
      (x x)))
    :in-theory
    (e/d (xef-chain-results)
         (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-eval)))))

(defthm xef-unit-inverse-evaluation-cancels
  (implies
   (xef-unit-cocycle-p c)
   (let* ((forward (xef-cocycle-eval c x))
          (backward
           (xef-cocycle-eval
            (xef-unit-cocycle-inverse c)
            (car forward))))
     (and (equal (car backward) (ifix x))
          (equal (+ (cdr forward)
                    (cdr backward))
                 0))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      xef-unit-inverse-evaluation-restores-state
      (c c)
      (x x))
     (:instance
      xef-unit-inverse-evaluation-negates-cost
      (c c)
      (x x)))
    :in-theory
    (e/d ()
         (xef-unit-cocycle-p
          xef-unit-cocycle-inverse
          xef-cocycle-eval)))))

(defthm xef-run-forward-then-backward
  (implies (xef-unit-table-p table)
           (let* ((forward
                   (xef-word-run word x table))
                  (backward
                   (xef-word-run
                    (xef-rev word)
                    (car forward)
                    (xef-invert-table table))))
             (and (equal (car backward) (ifix x))
                  (equal (+ (cdr forward)
                            (cdr backward))
                         0))))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-unit-inverse-evaluation-cancels
      (c (xef-word-summary word table))))
    :in-theory
    (e/d ()
         (xef-word-run
          xef-word-summary
          xef-rev
          xef-invert-table
          xef-unit-cocycle-inverse
          xef-cocycle-eval
          xef-unit-cocycle-p
          xef-unit-table-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 11. A final bridge: local edits with globally reversible semantics
;;
;; This theorem combines ropes, zipper contexts, bidirectional summaries, and
;; unit inversion.  It states that after a local replacement, the cached
;; forward program and the cached reverse-inverse program cancel exactly.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun xef-rope-backward-run (rope x table)
  (xef-word-run
   (xef-rev (xef-rope-flatten rope))
   x
   (xef-invert-table table)))

(defthm xef-replaced-rope-forward-then-backward
  (implies (xef-unit-table-p table)
           (let* ((rope
                   (xef-replace-focus new-focus context))
                  (forward
                   (xef-rope-forward-run rope x table))
                  (backward
                   (xef-rope-backward-run
                    rope
                    (car forward)
                    table)))
             (and (equal (car backward) (ifix x))
                  (equal (+ (cdr forward)
                            (cdr backward))
                         0))))
  :hints
  (("Goal"
    :use
    ((:instance
      xef-run-forward-then-backward
      (word
       (xef-rope-flatten
        (xef-replace-focus new-focus context)))))
    :in-theory
    (e/d (xef-rope-backward-run)
         (xef-replace-focus
          xef-rope-forward-run
          xef-rope-flatten
          xef-word-run
          xef-rev
          xef-invert-table
          xef-unit-table-p)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 12. A small user-facing RLE toolkit
;;
;; Sections 0--11 are the admitted ZZJ kernel.  This section is deliberately
;; less about extending the research object and more about making the existing
;; machinery pleasant to touch from ACL2-USER.
;;
;; A quick map for book users
;; --------------------------
;;
;;   Construct one command:
;;       (xef-cocycle a b p q)
;;
;;   Assemble a command table:
;;       (list (cons 'command-1 cocycle-1)
;;             (cons 'command-2 cocycle-2))
;;
;;   Execute an ordinary word:
;;       (xef-word-run word initial-state table)
;;
;;   Compile an ordinary word to one affine cocycle:
;;       (xef-word-summary word table)
;;
;;   Encode, clean, inspect, compile, or execute compressed words:
;;       xef-rle-encode
;;       xef-rle-canonicalize
;;       xef-rle-join
;;       xef-rle-decode
;;       xef-rle-symbol-count
;;       xef-rle-summary
;;       xef-rle-run
;;
;;   Inspect a compiled cocycle without depending on its cons representation:
;;       xef-cocycle-a, xef-cocycle-b, xef-cocycle-p, xef-cocycle-q
;;       xef-cocycle-eval
;;
;;   More advanced interfaces already present in the kernel:
;;       xef-word-bi-summary, xef-rope-summary, xef-plug-summary
;;       xef-cocycle-recenter, xef-linear-coboundary
;;       xef-unit-cocycle-inverse, xef-invert-table
;;
;; Users should normally avoid destructuring cocycles by CAR/CDR.  The
;; constructor, accessors, evaluator, composition laws, and summary functions
;; are the stable mathematical interface; the concrete nested-cons encoding is
;; merely an implementation choice.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Add one run to the front of an already-normalized tail.  Zero and malformed
; nonpositive counts disappear.  If the new symbol equals the first symbol of
; the tail, the two runs fuse.  This one operation is shared by the encoder and
; the normalizer, preventing two competing definitions of "canonical RLE".
(defun xef-rle-emit (symbol count runs)
  (let ((count (nfix count)))
    (cond ((zp count)
           runs)
          ((and (consp runs)
                (equal symbol (caar runs)))
           (cons (cons symbol
                       (+ count (nfix (cdar runs))))
                 (cdr runs)))
          (t
           (cons (cons symbol count)
                 runs)))))

(defun xef-rle-canonical-p (runs)
  (if (endp runs)
      t
    (and (consp (car runs))
         (posp (cdar runs))
         (or (endp (cdr runs))
             (not (equal (caar runs)
                         (caadr runs))))
         (xef-rle-canonical-p (cdr runs)))))

; Normalize without expanding.  The recursion normalizes the tail first and
; then XEF-RLE-EMIT decides whether to drop, prepend, or fuse the current run.
(defun xef-rle-canonicalize (runs)
  (if (endp runs)
      nil
    (xef-rle-emit
     (caar runs)
     (cdar runs)
     (xef-rle-canonicalize (cdr runs)))))

; A right-fold encoder.  It never constructs the expanded prefix twice and
; emits canonical output directly.
(defun xef-rle-encode (word)
  (if (endp word)
      nil
    (xef-rle-emit
     (car word)
     1
     (xef-rle-encode (cdr word)))))

; Compressed append with normalization and boundary fusion.  Defining JOIN in
; terms of CANONICALIZE gives it useful behavior even on untidy inputs, while
; its semantic theorem below explains it solely through decoded words.
(defun xef-rle-join (left right)
  (xef-rle-canonicalize (append left right)))

; The elementary list fact needed when two adjacent runs fuse.
(defthm xef-repeat-of-sum
  (equal (xef-repeat (+ (nfix m) (nfix n)) x)
         (append (xef-repeat m x)
                 (xef-repeat n x)))
  :hints (("Goal" :induct (xef-repeat m x))))

; XEF-RLE-EMIT is semantically just prepending COUNT copies of SYMBOL.
(defthm xef-rle-decode-of-emit
  (equal (xef-rle-decode
          (xef-rle-emit symbol count runs))
         (append (xef-repeat count symbol)
                 (xef-rle-decode runs)))
  :hints
  (("Goal"
    :in-theory
    (enable xef-rle-emit
            xef-rle-decode))))

(defthm xef-rle-canonical-p-of-emit
  (implies (xef-rle-canonical-p runs)
           (xef-rle-canonical-p
            (xef-rle-emit symbol count runs)))
  :hints
  (("Goal"
    :in-theory
    (enable xef-rle-emit
            xef-rle-canonical-p))))

; Canonicalization changes representation, not the represented word.
(defthm xef-rle-decode-of-canonicalize
  (equal (xef-rle-decode
          (xef-rle-canonicalize runs))
         (xef-rle-decode runs))
  :hints
  (("Goal"
    :induct (xef-rle-canonicalize runs)
    :in-theory
    (enable xef-rle-canonicalize))))

(defthm xef-rle-canonical-p-of-canonicalize
  (xef-rle-canonical-p
   (xef-rle-canonicalize runs))
  :hints
  (("Goal"
    :induct (xef-rle-canonicalize runs)
    :in-theory
    (enable xef-rle-canonicalize))))

; Keep the encoder/decoder interface one recursive layer at a time.  These
; two equations are intentionally separate from the round-trip theorem: they
; prevent ACL2 from opening both recursive definitions and inventing nested
; inductions over representation details.
(defthm xef-rle-encode-when-atom
  (implies (not (consp word))
           (equal (xef-rle-encode word) nil))
  :hints
  (("Goal"
    :in-theory (enable xef-rle-encode))))

(defthm xef-rle-decode-when-atom
  (implies (not (consp runs))
           (equal (xef-rle-decode runs) nil))
  :hints
  (("Goal"
    :in-theory (enable xef-rle-decode))))

; A one-element run is the bridge between the compressed decoder and
; ordinary CONS.  Keeping this fact separate prevents the encoder proof
; from opening the recursive definition of XEF-REPEAT.
(defthm xef-repeat-one
  (equal (xef-repeat 1 x)
         (list x))
  :hints
  (("Goal"
    :expand ((xef-repeat 1 x)))))

(defthm xef-append-repeat-one
  (equal (append (xef-repeat 1 x) ys)
         (cons x ys))
  :hints
  (("Goal"
    :in-theory (enable xef-repeat))))
(defthm xef-rle-decode-of-encode-step
  (implies (consp word)
           (equal (xef-rle-decode (xef-rle-encode word))
                  (cons (car word)
                        (xef-rle-decode
                         (xef-rle-encode (cdr word))))))
  :hints
  (("Goal"
    :expand ((xef-rle-encode word))
    :in-theory
    (e/d ()
         (xef-rle-encode
          xef-rle-emit
          xef-rle-decode
          xef-repeat
          xef-rle-decode-of-emit))
    :use
    ((:instance xef-rle-decode-of-emit
                (symbol (car word))
                (count 1)
                (runs (xef-rle-encode (cdr word))))))))

; The induction theorem below deliberately keeps the encoder and decoder
; opaque.  This base rule supplies the one observation needed in the END-P
; branch, just as XEF-RLE-DECODE-OF-ENCODE-STEP supplies the CONSP branch.
(defthm xef-rle-decode-of-encode-base
  (implies (endp word)
           (equal (xef-rle-decode (xef-rle-encode word))
                  nil))
  :hints
  (("Goal"
    :in-theory
    (enable xef-rle-encode
            xef-rle-decode))))

; Encoding followed by decoding recovers ACL2's total-list view of WORD.  The
; proof uses the induction machine generated by the encoder, but not its
; rewrite rule: only the induction rune is enabled.  Consequently the two
; small interface lemmas above, rather than expansion of the implementation,
; control the base and successor branches.
(defthm xef-rle-decode-of-encode
  (equal (xef-rle-decode (xef-rle-encode word))
         (true-list-fix word))
  :rule-classes nil
  :hints
  (("Goal"
    :induct (xef-rle-encode word)
    :in-theory
    (e/d ((:induction xef-rle-encode))
         ((:definition xef-rle-encode)
          xef-rle-emit
          xef-rle-decode)))))

(defthm xef-rle-decode-of-encode-when-true-listp
  (implies (true-listp word)
           (equal (xef-rle-decode (xef-rle-encode word))
                  word))
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-encode
                     (word word))))))

(defthm xef-rle-canonical-p-of-encode
  (xef-rle-canonical-p (xef-rle-encode word))
  :hints
  (("Goal"
    :induct (xef-rle-encode word)
    :in-theory
    (enable xef-rle-encode))))

(defthm xef-rle-decode-of-append
  (equal (xef-rle-decode (append left right))
         (append (xef-rle-decode left)
                 (xef-rle-decode right)))
  :hints
  (("Goal"
    :induct (xef-rle-decode left)
    :in-theory
    (enable xef-rle-decode))))

(defthm xef-rle-decode-of-join
  (equal (xef-rle-decode (xef-rle-join left right))
         (append (xef-rle-decode left)
                 (xef-rle-decode right)))
  :hints
  (("Goal"
    :in-theory
    (enable xef-rle-join))))

(defthm xef-rle-canonical-p-of-join
  (xef-rle-canonical-p (xef-rle-join left right))
  :hints
  (("Goal"
    :in-theory
    (enable xef-rle-join))))

; The remaining theorems lift the representation facts through the admitted
; semantic refinement laws.  Users can normalize or encode first without
; changing the compiled cocycle or the observable execution result.
(defthm xef-rle-summary-of-canonicalize
  (equal (xef-rle-summary
          (xef-rle-canonicalize runs)
          table)
         (xef-rle-summary runs table)))

(defthm xef-rle-run-of-canonicalize
  (equal (xef-rle-run
          (xef-rle-canonicalize runs)
          x
          table)
         (xef-rle-run runs x table)))

(defthm xef-rle-summary-of-encode
  (equal (xef-rle-summary
          (xef-rle-encode word)
          table)
         (xef-word-summary
          (true-list-fix word)
          table))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-encode
                     (word word))))))

(defthm xef-rle-summary-of-encode-when-true-listp
  (implies (true-listp word)
           (equal (xef-rle-summary
                   (xef-rle-encode word)
                   table)
                  (xef-word-summary word table)))
  :hints
  (("Goal"
    :use ((:instance xef-rle-summary-of-encode
                     (word word)
                     (table table))))))

(defthm xef-rle-run-of-encode
  (equal (xef-rle-run
          (xef-rle-encode word)
          x
          table)
         (xef-word-run
          (true-list-fix word)
          x
          table))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance xef-rle-decode-of-encode
                     (word word))))))

(defthm xef-rle-run-of-encode-when-true-listp
  (implies (true-listp word)
           (equal (xef-rle-run
                   (xef-rle-encode word)
                   x
                   table)
                  (xef-word-run word x table)))
  :hints
  (("Goal"
    :use ((:instance xef-rle-run-of-encode
                     (word word)
                     (x x)
                     (table table))))))

(defthm xef-rle-summary-of-join
  (equal (xef-rle-summary
          (xef-rle-join left right)
          table)
         (xef-cocycle-compose
          (xef-rle-summary right table)
          (xef-rle-summary left table))))

(defthm xef-rle-run-of-join
  (equal (xef-rle-run
          (xef-rle-join left right)
          x
          table)
         (let* ((first
                 (xef-rle-run left x table))
                (second
                 (xef-rle-run right
                              (car first)
                              table)))
           (xef-chain-results first second))))

(defxdoc xef-rle-toolkit
  :parents (xef-exotic-fertile-kernel)
  :short "Encode, normalize, join, compile, and execute run-length programs."
  :long
  "<p>An RLE program is a list of dotted pairs <tt>(symbol . count)</tt>.
  <tt>XEF-RLE-ENCODE</tt> compresses an ordinary true list,
  <tt>XEF-RLE-CANONICALIZE</tt> removes nonpositive runs and fuses equal
  neighbors, and <tt>XEF-RLE-JOIN</tt> concatenates compressed programs while
  normalizing the boundary.</p>

  <p><tt>XEF-RLE-DECODE</tt> exposes the represented word.
  <tt>XEF-RLE-SUMMARY</tt> instead compiles the compressed program directly to
  one affine cocycle, and <tt>XEF-RLE-RUN</tt> evaluates that summary.  For
  repeated evaluation at many initial states, compile once with
  <tt>XEF-RLE-SUMMARY</tt> and call <tt>XEF-COCYCLE-EVAL</tt> repeatedly.</p>

  <p>The principal representation laws are decoder preservation under
  canonicalization, encoder/decoder round trip, and decoder preservation under
  join.  Their summary and execution corollaries let client books normalize
  compressed data without changing observable behavior.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 13. Ground demonstrations
;;
;; ASSERT-EVENT is used only for small, concrete examples.  These examples are
;; not substitutes for the general theorems above; they are recognizable entry
;; points for a user learning what the interfaces calculate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Encoding discovers maximal adjacent runs.
(assert-event
 (equal (xef-rle-encode
         '(right right right left left right))
        '((right . 3)
          (left  . 2)
          (right . 1))))

; Canonicalization removes empty runs and fuses equal neighbors exposed by
; those removals.
(assert-event
 (equal (xef-rle-canonicalize
         '((right . 2)
           (right . 3)
           (left  . 0)
           (left  . -4)
           (left  . 2)
           (right . 1)))
        '((right . 5)
          (left  . 2)
          (right . 1))))

; JOIN fuses the touching RIGHT runs instead of leaving an artificial boundary.
(assert-event
 (equal (xef-rle-join
         '((right . 2))
         '((right . 3) (left . 1)))
        '((right . 5) (left . 1))))

; A number-line walker.  State is position; cost is the number of steps.
(defconst *xef-demo-walk-table*
  (list
   (cons 'right (xef-cocycle 1  1 0 1))
   (cons 'left  (xef-cocycle 1 -1 0 1))))

(assert-event
 (equal (xef-rle-run
         '((right . 7)
           (left  . 3)
           (right . 2))
         0
         *xef-demo-walk-table*)
        '(6 . 12)))

; "Increment and sample" computes an arithmetic progression.  Repeating the
; command five times from 3 observes 3+4+5+6+7 and finishes at 8.
(defconst *xef-demo-arithmetic-table*
  (list
   (cons 'step-and-sum
         (xef-cocycle 1 1 1 0))))

(assert-event
 (equal (xef-rle-run
         '((step-and-sum . 5))
         3
         *xef-demo-arithmetic-table*)
        '(8 . 25)))

; The summary is the closed form of that loop:
;     final-state = x + 5
;     total-cost  = 5*x + 10.
(assert-event
 (equal (xef-rle-summary
         '((step-and-sum . 5))
         *xef-demo-arithmetic-table*)
        (xef-cocycle 1 5 5 10)))

; "Double and sample" computes a geometric progression.  From 3, four rounds
; observe 3+6+12+24 and finish at 48.
(defconst *xef-demo-geometric-table*
  (list
   (cons 'double-and-sum
         (xef-cocycle 2 0 1 0))))

(assert-event
 (equal (xef-rle-run
         '((double-and-sum . 4))
         3
         *xef-demo-geometric-table*)
        '(48 . 45)))

(assert-event
 (equal (xef-rle-summary
         '((double-and-sum . 4))
         *xef-demo-geometric-table*)
        (xef-cocycle 16 0 15 0)))

; A potential-bearing table demonstrates certified accounting.  Each local
; cost is the change in the potential tau*x with tau=1, so total cost telescopes
; to final-state minus initial-state.
(defconst *xef-demo-potential-table*
  (list
   (cons 'increment
         (xef-linear-coboundary 1 1 1))
   (cons 'double
         (xef-linear-coboundary 1 2 0))))

(assert-event
 (xef-table-has-linear-potential-p
  1
  *xef-demo-potential-table*))

(assert-event
 (equal (xef-rle-run
         '((increment . 5)
           (double    . 2))
         3
         *xef-demo-potential-table*)
        '(32 . 29)))

; One can compile once and evaluate at many initial states.  This is often the
; most useful way to think about XEF-RLE-SUMMARY: it is a closed-form program.
(defconst *xef-demo-compiled-program*
  (xef-rle-summary
   '((increment . 5)
     (double    . 2))
   *xef-demo-potential-table*))

(assert-event
 (and
  (equal (xef-cocycle-eval
          *xef-demo-compiled-program*
          3)
         '(32 . 29))
  (equal (xef-cocycle-eval
          *xef-demo-compiled-program*
          10)
         '(60 . 50))))

; Suggested interactive expressions after INCLUDE-BOOK:
;
;   (xef-rle-encode '(a a a b b a))
;   (xef-rle-canonicalize '((a . 2) (a . 4) (b . 0) (c . 1)))
;   (xef-rle-decode '((a . 3) (b . 2) (a . 1)))
;   (xef-rle-symbol-count '((a . 3000) (b . 2000)))
;   (xef-rle-summary '((step-and-sum . 50))
;                    *xef-demo-arithmetic-table*)
;   (xef-cocycle-eval *xef-demo-compiled-program* 100)
;
; The first four expose representation behavior.  The last two expose the
; algebraic payoff: a compressed loop becomes one exact affine/cost summary.

; End of zzh-exotic-fertile-kernel.lisp
