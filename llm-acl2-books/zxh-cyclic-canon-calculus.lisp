; zxh-cyclic-canon-calculus.lisp
;
; A self-contained ACL2 book about finite cyclic rhythms, exact-cover canons,
; dihedral normalization, exhaustive search, and cartesian product canons.
;
; No SKIP-PROOFS, DEFAXIOM, trust tags, raw Lisp, program-mode definitions,
; or generated events are used.  All definitions are total ACL2 functions.

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zxh-cyclic-canon-calculus
  :parents (acl2::top)
  :short "Executable finite cyclic rhythms and mechanically certified exact-cover canons."
  :long
  "<p>A rhythm is a finite binary word.  Rotation makes it a pattern on a
  finite cycle; reflection and rotation generate its dihedral views.  A canon
  is a rhythm together with a list of cyclic shifts whose overlays cover every
  point exactly once.</p>

  <p>The book supplies executable normalization, onset extraction, period and
  primitive-root analysis, exhaustive canon search, a density theorem, and a
  cartesian product construction on finite tori.  The search theorem certifies
  every reported canon, while the product theorem builds larger exact covers
  from smaller ones.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Binary words
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-bit-fix (x)
  (if (equal x 0) 0 1))

(defun zxc-rhythm-fix (xs)
  (if (endp xs)
      nil
    (cons (zxc-bit-fix (car xs))
          (zxc-rhythm-fix (cdr xs)))))

(defun zxc-rhythmp (xs)
  (if (atom xs)
      (equal xs nil)
    (and (or (equal (car xs) 0)
             (equal (car xs) 1))
         (zxc-rhythmp (cdr xs)))))

(defthm zxc-rhythmp-of-rhythm-fix
  (zxc-rhythmp (zxc-rhythm-fix xs)))

(defthm zxc-true-listp-when-rhythmp
  (implies (zxc-rhythmp xs)
           (true-listp xs)))

(defthm zxc-true-list-fix-when-rhythmp
  (implies (zxc-rhythmp xs)
           (equal (true-list-fix xs) xs)))

(defthm zxc-rhythm-fix-when-rhythmp
  (implies (zxc-rhythmp xs)
           (equal (zxc-rhythm-fix xs) xs)))

(defthm zxc-rhythm-fix-idempotent
  (equal (zxc-rhythm-fix (zxc-rhythm-fix xs))
         (zxc-rhythm-fix xs)))

(defthm zxc-len-of-rhythm-fix
  (equal (len (zxc-rhythm-fix xs))
         (len xs)))

(defun zxc-weight (xs)
  (if (endp xs)
      0
    (+ (zxc-bit-fix (car xs))
       (zxc-weight (cdr xs)))))

(defun zxc-zeros (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (zxc-zeros (1- n)))))

(defun zxc-ones (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 1 (zxc-ones (1- n)))))

(defthm zxc-len-of-zeros
  (equal (len (zxc-zeros n))
         (nfix n)))

(defthm zxc-len-of-ones
  (equal (len (zxc-ones n))
         (nfix n)))

(defthm zxc-weight-of-zeros
  (equal (zxc-weight (zxc-zeros n)) 0))

(defthm zxc-weight-of-ones
  (equal (zxc-weight (zxc-ones n))
         (nfix n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Cyclic and dihedral actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-rotate1 (xs)
  (if (endp xs)
      nil
    (append (cdr xs) (list (car xs)))))

(defun zxc-rotate (k xs)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (true-list-fix xs)
    (zxc-rotate (1- k) (zxc-rotate1 xs))))

(defun zxc-reflect (xs)
  (reverse (true-list-fix xs)))

(defthm zxc-len-of-rotate1
  (equal (len (zxc-rotate1 xs))
         (len xs)))

(defthm zxc-len-of-rotate
  (equal (len (zxc-rotate k xs))
         (len xs)))

(defthm zxc-rhythmp-of-rotate1
  (implies (zxc-rhythmp xs)
           (zxc-rhythmp (zxc-rotate1 xs))))

(defthm zxc-rhythmp-of-rotate
  (implies (zxc-rhythmp xs)
           (zxc-rhythmp (zxc-rotate k xs))))

(defthm zxc-rhythmp-of-reflect
  (implies (zxc-rhythmp xs)
           (zxc-rhythmp (zxc-reflect xs))))

(defthm zxc-weight-of-append
  (equal (zxc-weight (append xs ys))
         (+ (zxc-weight xs)
            (zxc-weight ys))))

(defthm zxc-weight-of-rotate1
  (equal (zxc-weight (zxc-rotate1 xs))
         (zxc-weight xs)))

(defthm zxc-weight-of-rotate
  (equal (zxc-weight (zxc-rotate k xs))
         (zxc-weight xs)))

(defthm zxc-rotate-of-sum
  (equal (zxc-rotate (+ (nfix m) (nfix n)) xs)
         (zxc-rotate n (zxc-rotate m xs)))
  :hints (("Goal" :induct (zxc-rotate n (zxc-rotate m xs)))))

(defthm zxc-reflect-involution
  (equal (zxc-reflect (zxc-reflect xs))
         (true-list-fix xs)))

(defun zxc-rotations-aux (fuel xs)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (cons (true-list-fix xs)
          (zxc-rotations-aux (1- fuel)
                             (zxc-rotate1 xs)))))

(defun zxc-rotations (xs)
  (let ((r (zxc-rhythm-fix xs)))
    (zxc-rotations-aux (len r) r)))

(defun zxc-dihedral-orbit (xs)
  (let ((r (zxc-rhythm-fix xs)))
    (append (zxc-rotations r)
            (zxc-rotations (zxc-reflect r)))))

(defun zxc-word-rank (xs)
  (if (endp xs)
      0
    (+ (zxc-bit-fix (car xs))
       (* 2 (zxc-word-rank (cdr xs))))))

(defun zxc-rank-min (a b)
  (if (<= (zxc-word-rank a)
          (zxc-word-rank b))
      a
    b))

(defun zxc-minimum-view (views)
  (if (endp views)
      nil
    (if (endp (cdr views))
        (car views)
      (zxc-rank-min (car views)
                    (zxc-minimum-view (cdr views))))))

(defun zxc-dihedral-normalize (xs)
  (zxc-minimum-view (zxc-dihedral-orbit xs)))

(defun zxc-no-higher-rankp (candidate views)
  (if (endp views)
      t
    (and (<= (zxc-word-rank candidate)
             (zxc-word-rank (car views)))
         (zxc-no-higher-rankp candidate (cdr views)))))

(defthm zxc-minimum-view-member
  (implies (consp views)
           (member-equal (zxc-minimum-view views) views)))

(defthm zxc-no-higher-rankp-when-lower
  (implies (and (<= (zxc-word-rank a)
                    (zxc-word-rank b))
                (zxc-no-higher-rankp b views))
           (zxc-no-higher-rankp a views)))

(defthm zxc-minimum-view-is-minimal
  (zxc-no-higher-rankp (zxc-minimum-view views) views)
  :hints (("Goal"
           :induct (zxc-minimum-view views)
           :in-theory (enable zxc-minimum-view zxc-rank-min))))

(defthm zxc-dihedral-normalize-is-a-view
  (implies (consp xs)
           (member-equal (zxc-dihedral-normalize xs)
                         (zxc-dihedral-orbit xs))))

(defthm zxc-dihedral-normalize-is-minimal
  (zxc-no-higher-rankp (zxc-dihedral-normalize xs)
                       (zxc-dihedral-orbit xs)))

(defun zxc-rhythm-listp (views)
  (if (endp views)
      t
    (and (zxc-rhythmp (car views))
         (zxc-rhythm-listp (cdr views)))))

(defthm zxc-rhythm-listp-of-append
  (equal (zxc-rhythm-listp (append xs ys))
         (and (zxc-rhythm-listp xs)
              (zxc-rhythm-listp ys))))

(defthm zxc-rhythm-listp-of-rotations-aux
  (implies (zxc-rhythmp xs)
           (zxc-rhythm-listp (zxc-rotations-aux fuel xs)))
  :hints (("Goal"
           :induct (zxc-rotations-aux fuel xs)
           :in-theory (e/d (zxc-rotations-aux
                            zxc-rhythm-listp)
                           (zxc-rhythmp
                            zxc-rotate1)))))

(defthm zxc-rhythm-listp-of-dihedral-orbit
  (zxc-rhythm-listp (zxc-dihedral-orbit xs)))

(defthm zxc-rhythmp-of-minimum-view
  (implies (zxc-rhythm-listp views)
           (zxc-rhythmp (zxc-minimum-view views)))
  :hints (("Goal"
           :induct (zxc-minimum-view views)
           :in-theory (enable zxc-minimum-view
                              zxc-rank-min
                              zxc-rhythm-listp))))

(defthm zxc-rhythmp-of-dihedral-normalize
  (zxc-rhythmp (zxc-dihedral-normalize xs))
  :hints (("Goal"
           :use ((:instance zxc-rhythmp-of-minimum-view
                            (views (zxc-dihedral-orbit xs))))
           :in-theory (disable zxc-rhythmp-of-minimum-view
                               zxc-rhythm-listp-of-dihedral-orbit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Periods and primitive roots
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-periodp (k xs)
  (equal (zxc-rotate k (zxc-rhythm-fix xs))
         (zxc-rhythm-fix xs)))

(defun zxc-find-proper-period-aux (fuel k xs)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      0
    (if (zxc-periodp k xs)
        (nfix k)
      (zxc-find-proper-period-aux (1- fuel)
                                  (+ 1 (nfix k))
                                  xs))))

(defun zxc-proper-period-witness (xs)
  (let ((n (len (zxc-rhythm-fix xs))))
    (if (zp n)
        0
      (zxc-find-proper-period-aux (1- n) 1 xs))))

(defun zxc-primitivep (xs)
  (equal (zxc-proper-period-witness xs) 0))

(defthm zxc-find-proper-period-aux-sound
  (implies (not (equal (zxc-find-proper-period-aux fuel k xs) 0))
           (zxc-periodp (zxc-find-proper-period-aux fuel k xs) xs)))

(defthm zxc-proper-period-witness-sound
  (implies (not (equal (zxc-proper-period-witness xs) 0))
           (zxc-periodp (zxc-proper-period-witness xs) xs)))

(defun zxc-take (n xs)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (endp xs))
      nil
    (cons (car xs)
          (zxc-take (1- n) (cdr xs)))))

(defun zxc-drop (n xs)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (endp xs))
      (true-list-fix xs)
    (zxc-drop (1- n) (cdr xs))))

(defun zxc-prefixp (prefix xs)
  (if (endp prefix)
      t
    (and (consp xs)
         (equal (car prefix) (car xs))
         (zxc-prefixp (cdr prefix) (cdr xs)))))

(defun zxc-blocks-p-aux (fuel block xs)
  (declare (xargs :measure (nfix fuel)))
  (cond ((endp xs)
         t)
        ((or (zp fuel) (endp block))
         nil)
        (t
         (and (zxc-prefixp block xs)
              (zxc-blocks-p-aux (1- fuel)
                                block
                                (zxc-drop (len block) xs))))))

(defun zxc-rootp (root xs)
  (let ((r (zxc-rhythm-fix xs))
        (q (zxc-rhythm-fix root)))
    (if (endp r)
        (endp q)
      (and (consp q)
           (zxc-blocks-p-aux (len r) q r)))))

(defthm zxc-prefixp-reflexive
  (zxc-prefixp xs xs))

(defthm zxc-drop-of-len
  (equal (zxc-drop (len xs) xs) nil))

(defthm zxc-blocks-p-aux-reflexive
  (implies (consp xs)
           (zxc-blocks-p-aux (len xs) xs xs))
  :hints (("Goal"
           :in-theory (enable zxc-blocks-p-aux))))

(defthm zxc-rootp-reflexive
  (zxc-rootp (zxc-rhythm-fix xs) xs)
  :hints (("Goal"
           :use ((:instance zxc-blocks-p-aux-reflexive
                            (xs (zxc-rhythm-fix xs))))
           :in-theory (enable zxc-rootp))))

(defun zxc-find-root-aux (fuel size xs)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (zxc-rhythm-fix xs)
    (let ((candidate (zxc-take size (zxc-rhythm-fix xs))))
      (if (zxc-rootp candidate xs)
          candidate
        (zxc-find-root-aux (1- fuel)
                           (+ 1 (nfix size))
                           xs)))))

(defun zxc-primitive-root (xs)
  (let ((r (zxc-rhythm-fix xs)))
    (if (endp r)
        nil
      (zxc-find-root-aux (len r) 1 r))))

(defthm zxc-find-root-aux-sound
  (zxc-rootp (zxc-find-root-aux fuel size xs) xs)
  :hints (("Goal"
           :induct (zxc-find-root-aux fuel size xs)
           :in-theory (e/d (zxc-find-root-aux)
                           (zxc-rootp
                            zxc-blocks-p-aux
                            zxc-take)))))

(defthm zxc-rootp-of-rhythm-fix-right
  (equal (zxc-rootp root (zxc-rhythm-fix xs))
         (zxc-rootp root xs))
  :hints (("Goal" :in-theory (enable zxc-rootp))))

(defthm zxc-primitive-root-as-find-root
  (equal (zxc-primitive-root xs)
         (zxc-find-root-aux (len (zxc-rhythm-fix xs))
                            1
                            (zxc-rhythm-fix xs)))
  :hints (("Goal" :in-theory (enable zxc-primitive-root))))

(defthm zxc-primitive-root-sound
  (zxc-rootp (zxc-primitive-root xs) xs)
  :hints (("Goal"
           :use ((:instance zxc-find-root-aux-sound
                            (fuel (len (zxc-rhythm-fix xs)))
                            (size 1)
                            (xs (zxc-rhythm-fix xs))))
           :in-theory (disable zxc-find-root-aux-sound))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Onsets and exact-cover canons
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-onsets-aux (index xs)
  (if (endp xs)
      nil
    (if (equal (zxc-bit-fix (car xs)) 1)
        (cons (nfix index)
              (zxc-onsets-aux (+ 1 (nfix index)) (cdr xs)))
      (zxc-onsets-aux (+ 1 (nfix index)) (cdr xs)))))

(defun zxc-onsets (xs)
  (zxc-onsets-aux 0 (zxc-rhythm-fix xs)))

(defun zxc-shifted-onsets (shift xs)
  (zxc-onsets (zxc-rotate shift (zxc-rhythm-fix xs))))

(defthm zxc-len-of-onsets-aux
  (equal (len (zxc-onsets-aux index xs))
         (zxc-weight xs))
  :hints (("Goal"
           :induct (zxc-onsets-aux index xs)
           :in-theory (enable zxc-onsets-aux zxc-weight))))

(defthm zxc-weight-of-rhythm-fix
  (equal (zxc-weight (zxc-rhythm-fix xs))
         (zxc-weight xs)))

(defthm zxc-len-of-onsets-is-weight
  (equal (len (zxc-onsets xs))
         (zxc-weight xs))
  :hints (("Goal" :in-theory (enable zxc-onsets))))

(defun zxc-add-words (xs ys)
  (if (endp xs)
      nil
    (cons (+ (ifix (car xs))
             (ifix (car ys)))
          (zxc-add-words (cdr xs) (cdr ys)))))

(defthm zxc-len-of-add-words
  (equal (len (zxc-add-words xs ys))
         (len xs)))

(defun zxc-integer-sum (xs)
  (if (endp xs)
      0
    (+ (ifix (car xs))
       (zxc-integer-sum (cdr xs)))))

(defthm zxc-integer-sum-of-add-words
  (implies (equal (len xs) (len ys))
           (equal (zxc-integer-sum (zxc-add-words xs ys))
                  (+ (zxc-integer-sum xs)
                     (zxc-integer-sum ys)))))

(defthm zxc-integer-sum-of-rhythm
  (equal (zxc-integer-sum (zxc-rhythm-fix xs))
         (zxc-weight xs)))

(defthm zxc-integer-sum-of-zeros
  (equal (zxc-integer-sum (zxc-zeros n)) 0))

(defthm zxc-integer-sum-of-ones
  (equal (zxc-integer-sum (zxc-ones n))
         (nfix n)))

(defthm zxc-integer-sum-of-rotate-rhythm
  (equal (zxc-integer-sum
          (zxc-rotate k (zxc-rhythm-fix xs)))
         (zxc-weight xs))
  :hints (("Goal"
           :use ((:instance zxc-integer-sum-of-rhythm
                            (xs (zxc-rotate k (zxc-rhythm-fix xs)))))
           :in-theory (disable zxc-integer-sum-of-rhythm))))

(defun zxc-overlay (shifts rhythm)
  (let ((r (zxc-rhythm-fix rhythm)))
    (if (endp shifts)
        (zxc-zeros (len r))
      (zxc-add-words (zxc-rotate (nfix (car shifts)) r)
                     (zxc-overlay (cdr shifts) r)))))

(defthm zxc-len-of-overlay
  (equal (len (zxc-overlay shifts rhythm))
         (len rhythm)))

(defthm zxc-integer-sum-of-overlay
  (equal (zxc-integer-sum (zxc-overlay shifts rhythm))
         (* (len shifts)
            (zxc-weight rhythm)))
  :hints (("Goal"
           :induct (zxc-overlay shifts rhythm)
           :in-theory (enable zxc-overlay))))

(defun zxc-exact-coverp (rhythm shifts)
  (equal (zxc-overlay shifts rhythm)
         (zxc-ones (len (zxc-rhythm-fix rhythm)))))

(defun zxc-canon (rhythm shifts)
  (list (zxc-rhythm-fix rhythm)
        (true-list-fix shifts)))

(defun zxc-canon-rhythm (canon)
  (car canon))

(defun zxc-canon-shifts (canon)
  (cadr canon))

(defun zxc-canonp (canon)
  (and (consp canon)
       (consp (cdr canon))
       (endp (cddr canon))
       (zxc-exact-coverp (zxc-canon-rhythm canon)
                         (zxc-canon-shifts canon))))

(defthm zxc-exact-cover-density-law
  (implies (zxc-exact-coverp rhythm shifts)
           (equal (* (len shifts)
                     (zxc-weight rhythm))
                  (len rhythm)))
  :hints (("Goal"
           :use ((:instance zxc-integer-sum-of-overlay)
                 (:instance zxc-integer-sum-of-ones
                            (n (len (zxc-rhythm-fix rhythm)))))
           :in-theory (e/d (zxc-exact-coverp)
                           (zxc-integer-sum-of-overlay
                            zxc-integer-sum-of-ones
                            zxc-overlay
                            zxc-ones
                            zxc-integer-sum
                            zxc-weight)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Exhaustive finite search
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-iota-aux (index fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (cons (nfix index)
          (zxc-iota-aux (+ 1 (nfix index))
                        (1- fuel)))))

(defun zxc-iota (n)
  (zxc-iota-aux 0 n))

(defun zxc-cons-each (x xss)
  (if (endp xss)
      nil
    (cons (cons x (car xss))
          (zxc-cons-each x (cdr xss)))))

(defun zxc-subsets (xs)
  (if (endp xs)
      (list nil)
    (let ((rest (zxc-subsets (cdr xs))))
      (append rest
              (zxc-cons-each (car xs) rest)))))

(defun zxc-filter-canons (rhythm candidates)
  (if (endp candidates)
      nil
    (let ((canon (zxc-canon rhythm (car candidates))))
      (if (zxc-canonp canon)
          (cons canon
                (zxc-filter-canons rhythm (cdr candidates)))
        (zxc-filter-canons rhythm (cdr candidates))))))

(defun zxc-search-canons (rhythm)
  (let ((r (zxc-rhythm-fix rhythm)))
    (zxc-filter-canons r
                       (zxc-subsets (zxc-iota (len r))))))

(defthm zxc-member-of-filter-canons-is-canon
  (implies (member-equal canon
                         (zxc-filter-canons rhythm candidates))
           (zxc-canonp canon)))

(defthm zxc-search-canons-sound
  (implies (member-equal canon (zxc-search-canons rhythm))
           (zxc-canonp canon)))

(defthm zxc-filter-canons-complete-for-candidate
  (implies (and (member-equal shifts candidates)
                (zxc-canonp (zxc-canon rhythm shifts)))
           (member-equal (zxc-canon rhythm shifts)
                         (zxc-filter-canons rhythm candidates))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Product canons on finite tori
;;
;; The cartesian product of exact covers on C_m and C_n is an exact cover on
;; C_m x C_n.  Profiles make the proof transparent: the product profile is the
;; outer product of the two one-dimensional profiles.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zxc-scale-word (c xs)
  (if (endp xs)
      nil
    (cons (* (ifix c) (ifix (car xs)))
          (zxc-scale-word c (cdr xs)))))

(defun zxc-outer-product (xs ys)
  (if (endp xs)
      nil
    (cons (zxc-scale-word (car xs) ys)
          (zxc-outer-product (cdr xs) ys))))

(defun zxc-all-onesp (xs)
  (if (endp xs)
      t
    (and (equal (car xs) 1)
         (zxc-all-onesp (cdr xs)))))

(defun zxc-all-ones-gridp (grid)
  (if (endp grid)
      t
    (and (zxc-all-onesp (car grid))
         (zxc-all-ones-gridp (cdr grid)))))

(defun zxc-torus-profile (rhythm-a shifts-a rhythm-b shifts-b)
  (zxc-outer-product (zxc-overlay shifts-a rhythm-a)
                     (zxc-overlay shifts-b rhythm-b)))

(defun zxc-torus-exact-coverp (rhythm-a shifts-a rhythm-b shifts-b)
  (zxc-all-ones-gridp
   (zxc-torus-profile rhythm-a shifts-a rhythm-b shifts-b)))

(defthm zxc-all-onesp-of-ones
  (zxc-all-onesp (zxc-ones n)))

(defthm zxc-scale-one-over-ones
  (equal (zxc-scale-word 1 (zxc-ones n))
         (zxc-ones n)))

(defthm zxc-outer-product-of-ones
  (zxc-all-ones-gridp
   (zxc-outer-product (zxc-ones m)
                      (zxc-ones n))))

(defthm zxc-product-canon-sound
  (implies (and (zxc-exact-coverp rhythm-a shifts-a)
                (zxc-exact-coverp rhythm-b shifts-b))
           (zxc-torus-exact-coverp rhythm-a shifts-a
                                   rhythm-b shifts-b)))

(defun zxc-pair-with-each (x ys)
  (if (endp ys)
      nil
    (cons (cons x (car ys))
          (zxc-pair-with-each x (cdr ys)))))

(defun zxc-cartesian-shifts (xs ys)
  (if (endp xs)
      nil
    (append (zxc-pair-with-each (car xs) ys)
            (zxc-cartesian-shifts (cdr xs) ys))))

(defthm zxc-len-of-pair-with-each
  (equal (len (zxc-pair-with-each x ys))
         (len ys)))

(defthm zxc-len-of-cartesian-shifts
  (equal (len (zxc-cartesian-shifts xs ys))
         (* (len xs) (len ys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Recognizable examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zxc-tresillo-six*
  '(1 0 0 1 0 0))

(defconst *zxc-three-voices*
  '(0 1 2))

(assert-event
 (zxc-exact-coverp *zxc-tresillo-six* *zxc-three-voices*))

(assert-event
 (equal (zxc-overlay *zxc-three-voices* *zxc-tresillo-six*)
        '(1 1 1 1 1 1)))

(assert-event
 (member-equal (zxc-canon *zxc-tresillo-six* *zxc-three-voices*)
               (zxc-search-canons *zxc-tresillo-six*)))

(defconst *zxc-quarter-pulse*
  '(1 0 0 0))

(defconst *zxc-four-voices*
  '(0 1 2 3))

(assert-event
 (zxc-exact-coverp *zxc-quarter-pulse* *zxc-four-voices*))

(assert-event
 (zxc-torus-exact-coverp
  *zxc-tresillo-six* *zxc-three-voices*
  *zxc-quarter-pulse* *zxc-four-voices*))

(assert-event
 (equal (len (zxc-cartesian-shifts *zxc-three-voices*
                                   *zxc-four-voices*))
        12))

(defconst *zxc-periodic-example*
  '(1 0 0 1 0 0 1 0 0 1 0 0))

(assert-event
 (equal (zxc-primitive-root *zxc-periodic-example*)
        '(1 0 0)))

(assert-event
 (zxc-rootp (zxc-primitive-root *zxc-periodic-example*)
            *zxc-periodic-example*))

(defconst *zxc-dihedral-example*
  '(1 0 1 1 0 0))

(assert-event
 (member-equal (zxc-dihedral-normalize *zxc-dihedral-example*)
               (zxc-dihedral-orbit *zxc-dihedral-example*)))

(defxdoc zxc-user-interface
  :parents (zxh-cyclic-canon-calculus)
  :short "The ordinary interface for rhythm and canon experiments."
  :long
  "<p>Normalize arbitrary lists with <tt>ZXC-RHYTHM-FIX</tt>.  Use
  <tt>ZXC-ROTATE</tt>, <tt>ZXC-REFLECT</tt>, and
  <tt>ZXC-DIHEDRAL-NORMALIZE</tt> for cyclic and dihedral structure.
  <tt>ZXC-PRIMITIVE-ROOT</tt> finds a repeated block certified by
  <tt>ZXC-ROOTP</tt>.</p>

  <p><tt>ZXC-OVERLAY</tt> computes the occupancy profile of translated voices.
  <tt>ZXC-EXACT-COVERP</tt> recognizes exact-cover canons, and
  <tt>ZXC-SEARCH-CANONS</tt> exhaustively searches all subsets of shifts on the
  cycle.  Every returned object satisfies <tt>ZXC-CANONP</tt>.</p>

  <p><tt>ZXC-TORUS-EXACT-COVERP</tt> and
  <tt>ZXC-PRODUCT-CANON-SOUND</tt> combine two one-dimensional canons into an
  exact cover on the cartesian product of their cycles.  The corresponding
  voice set is generated by <tt>ZXC-CARTESIAN-SHIFTS</tt>.</p>")
