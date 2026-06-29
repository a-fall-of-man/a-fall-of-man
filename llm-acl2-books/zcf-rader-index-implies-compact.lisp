; Every finite Rader index certificate already carries its compact bank.
(in-package "ACL2")

(include-book "zce-universal-rader-toom-cook-composition")
(include-book "zcc-universal-generated-rader-certificate")
(include-book "zcf0-finite-residue-permutation")
(include-book "kestrel/utilities/lists/index-of-theorems" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/lists-light/nthcdr" :dir :system)

; Broad Toom--Cook arithmetic rules are excellent in their native proof
; context but loop on the generic inequalities below.
(in-theory
 (disable tc-node-before-current-implies-before-bound
          tc-less-natural-implies-distinct
          tc-current-point-below-bound
          tc-not-zp-count-when-natural-below))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Rader position is the clean finite-list position from the prelude.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-rgi-position-is-zcf-position
  (equal (rgi-position x xs)
         (zcf-position x xs))
  :hints
  (("Goal"
    :induct (rgi-position x xs)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-position zcf-position)))))

(defthm zcf-natp-of-rgi-position
  (natp (rgi-position x xs))
  :hints
  (("Goal"
    :use ((:instance zcf-natp-of-position))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcf-rgi-position-is-zcf-position)))))

(defthm zcf-rgi-position-of-nth
  (implies (and (rgi-permutationp p xs)
                (natp i)
                (< i (len xs)))
           (equal (rgi-position (nth i xs) xs)
                  i))
  :hints
  (("Goal"
    :use ((:instance zcf-positive-residues-imply-nat-listp)
          (:instance zcf-position-of-nth))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp zcf-rgi-position-is-zcf-position)))))

(defthm zcf-nth-of-rgi-position
  (implies (and (rgi-permutationp p xs)
                (posp x)
                (< x (nfix p)))
           (equal (nth (rgi-position x xs) xs)
                  x))
  :hints
  (("Goal"
    :use ((:instance zcf-member-of-rgi-permutation)
          (:instance zcf-positive-residues-imply-nat-listp)
          (:instance zcf-nth-of-position))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp zcf-rgi-position-is-zcf-position posp natp)))))

(defthm zcf-rgi-position-less-than-len
  (implies (and (rgi-permutationp p xs)
                (posp x)
                (< x (nfix p)))
           (< (rgi-position x xs) (len xs)))
  :rule-classes :linear
  :hints
  (("Goal"
    :use ((:instance zcf-member-of-rgi-permutation)
          (:instance zcf-positive-residues-imply-nat-listp)
          (:instance zcf-position-less-than-len))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp zcf-rgi-position-is-zcf-position posp natp)))))

(defthm zcf-equal-of-nth-when-no-duplicatesp
  (implies (and (natp i) (< i (len xs))
                (natp j) (< j (len xs))
                (no-duplicatesp-equal xs))
           (equal (equal (nth i xs) (nth j xs))
                  (equal i j)))
  :hints
  (("Goal"
    :use ((:instance index-of-nth-when-no-duplicatesp
                     (i i) (x xs))
          (:instance index-of-nth-when-no-duplicatesp
                     (i j) (x xs)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(integer-range-p natp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extract arbitrary entries from the nested finite relation certificate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-relation-rowp-head
  (implies
   (and (rgi-relation-rowp count a p inputs kernels outputs)
        (not (zp count)))
   (equal
    (nth (mod (- (1- (nfix count)) (nfix a))
              (1- (nfix p)))
         kernels)
    (mod (* (nth (nfix a) inputs)
            (nth (1- (nfix count)) outputs))
         (nfix p))))
  :hints
  (("Goal"
    :use ((:instance rgi-relation-rowp-open))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relation-rowp-open)))))

(defthm zcf-relation-rowp-tail
  (implies
   (and (rgi-relation-rowp count a p inputs kernels outputs)
        (not (zp count)))
   (rgi-relation-rowp (1- count) a p inputs kernels outputs))
  :hints
  (("Goal"
    :use ((:instance rgi-relation-rowp-open))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relation-rowp-open)))))

(defthm zcf-relation-rowp-entry
  (implies
   (and (rgi-relation-rowp count a p inputs kernels outputs)
        (natp m)
        (< m (nfix count)))
   (equal
    (nth (mod (- m (nfix a)) (1- (nfix p))) kernels)
    (mod (* (nth (nfix a) inputs)
            (nth m outputs))
         (nfix p))))
  :hints
  (("Goal"
    :induct (rcb-countdown-induct count m)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rcb-countdown-induct
       rcb-nfix-of-predecessor
       rcb-index-below-predecessor
       rcb-zp-no-bounded-nat
       rcb-last-index-implies-not-zp
       zcf-relation-rowp-head
       zcf-relation-rowp-tail)))))

(defthm zcf-relationp-aux-head
  (implies
   (and (rgi-relationp-aux count p inputs kernels outputs)
        (not (zp count)))
   (rgi-relation-rowp
    (1- (nfix p)) (1- (nfix count)) p inputs kernels outputs))
  :hints
  (("Goal"
    :use ((:instance rgi-relationp-aux-open))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relationp-aux-open)))))

(defthm zcf-relationp-aux-tail
  (implies
   (and (rgi-relationp-aux count p inputs kernels outputs)
        (not (zp count)))
   (rgi-relationp-aux (1- count) p inputs kernels outputs))
  :hints
  (("Goal"
    :use ((:instance rgi-relationp-aux-open))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relationp-aux-open)))))

(defthm zcf-relationp-aux-row
  (implies
   (and (rgi-relationp-aux count p inputs kernels outputs)
        (natp a)
        (< a (nfix count)))
   (rgi-relation-rowp
    (1- (nfix p)) a p inputs kernels outputs))
  :hints
  (("Goal"
    :induct (rcb-countdown-induct count a)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rcb-countdown-induct
       rcb-nfix-of-predecessor
       rcb-index-below-predecessor
       rcb-zp-no-bounded-nat
       rcb-last-index-implies-not-zp
       zcf-relationp-aux-head
       zcf-relationp-aux-tail)))))

(defthm zcf-index-certificate-relation-entry
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp a)
        (< a (1- (nfix p)))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (nth (mod (- m a) (1- (nfix p))) kernels)
    (mod (* (nth a inputs) (nth m outputs))
         (nfix p))))
  :hints
  (("Goal"
    :use
    ((:instance rgi-index-certificate-implies-relation)
     (:instance zcf-relationp-aux-row
                (count (1- (nfix p))))
     (:instance zcf-relation-rowp-entry
                (count (1- (nfix p)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(nfix natp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The cyclic-convolution index equation is the Rader difference equation.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-cyclic-sum-index
  (implies (and (posp n)
                (natp a) (< a n)
                (natp b) (< b n)
                (natp m) (< m n))
           (equal (equal (mod (+ a b) n) m)
                  (equal b (mod (- m a) n))))
  :hints
  (("Goal"
    :use
    ((:instance equal-of-mod-of-+-and-mod-of-+-cancel
                (x a)
                (x1 b)
                (x2 (- m a))
                (y n)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(posp natp mod-when-<)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Certificate consequences in positional form.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-index-certificate-size
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (and (< 2 (nfix p))
                (natp p)
                (equal (nfix p) p)
                (posp p)
                (posp (nfix p))
                (posp (1- (nfix p)))
                (natp (1- (nfix p)))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-index-certificatep posp natp nfix)))))

(defthm zcf-len-of-rgi-permutation
  (implies (rgi-permutationp p xs)
           (equal (len xs) (1- (nfix p))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp)))))

(defthm zcf-position-zero-of-permutation
  (implies (rgi-permutationp p xs)
           (equal (rgi-position 0 xs)
                  (1- (nfix p))))
  :hints
  (("Goal"
    :use ((:instance zcf-position-zero-in-positive-residues))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp zcf-rgi-position-is-zcf-position)))))

(defthm zcf-position-below-rader-size
  (implies (and (rgi-permutationp p xs)
                (posp x)
                (< x (nfix p)))
           (< (rgi-position x xs)
              (1- (nfix p))))
  :rule-classes :linear
  :hints
  (("Goal"
    :use ((:instance zcf-rgi-position-less-than-len))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp)))))

(defthm zcf-index-relation-at-input-position
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp row)
        (< row (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (nth (mod (- m (rgi-position row inputs))
              (1- (nfix p)))
         kernels)
    (mod (* row (nth m outputs))
         (nfix p))))
  :hints
  (("Goal"
    :use
    ((:instance rgi-index-certificate-implies-input-permutation)
     (:instance zcf-position-below-rader-size
                (xs inputs) (x row))
     (:instance zcf-natp-of-rgi-position
                (x row) (xs inputs))
     (:instance zcf-nth-of-rgi-position
                (xs inputs) (x row))
     (:instance zcf-index-certificate-relation-entry
                (a (rgi-position row inputs))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(posp natp)))))

(defthm zcf-mod-index-range
  (implies (and (posp n)
                (integerp x))
           (and (natp (mod x n))
                (< (mod x n) n)))
  :hints
  (("Goal"
    :use ((:instance mod-bound-linear-arg2 (x x) (y n)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(posp natp <-of-mod-and-0 integerp-of-mod-type)))))

(defthm zcf-index-relation-product-positive
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp row)
        (< row (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (posp (mod (* row (nth m outputs))
              (nfix p))))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs kernels))
     (:instance zcf-natp-of-rgi-position
                (x row) (xs inputs))
     (:instance zcf-mod-index-range
                (n (1- (nfix p)))
                (x (- m (rgi-position row inputs))))
     (:instance zcf-permutation-residue-of-nth
                (xs kernels)
                (i (mod (- m (rgi-position row inputs))
                        (1- (nfix p)))))
     (:instance zcf-index-relation-at-input-position))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(posp natp)))))

(defthm zcf-column-matches-rader-product-iff-difference-position
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp row)
        (< row (nfix p))
        (posp column)
        (< column (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (equal column
           (mod (* row (nth m outputs)) (nfix p)))
    (equal
     (rgi-position column kernels)
     (mod (- m (rgi-position row inputs))
          (1- (nfix p))))))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-input-permutation)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs kernels))
     (:instance zcf-natp-of-rgi-position
                (x row) (xs inputs))
     (:instance zcf-natp-of-rgi-position
                (x column) (xs kernels))
     (:instance zcf-position-below-rader-size
                (xs kernels) (x column))
     (:instance zcf-nth-of-rgi-position
                (xs kernels) (x column))
     (:instance zcf-mod-index-range
                (n (1- (nfix p)))
                (x (- m (rgi-position row inputs))))
     (:instance zcf-index-relation-at-input-position)
     (:instance zcf-equal-of-nth-when-no-duplicatesp
                (xs kernels)
                (i (rgi-position column kernels))
                (j (mod (- m (rgi-position row inputs))
                        (1- (nfix p))))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-permutationp posp natp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pointwise compact/Fourier equality.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-positive-row-column-entry
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp row)
        (< row (nfix p))
        (posp column)
        (< column (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (rgi-lifted-entry (1- (nfix p)) m
                      row column inputs kernels)
    (rgi-fourier-entry p (nth m outputs) row column)))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-input-permutation)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance rgi-index-certificate-implies-output-permutation)
     (:instance zcf-len-of-rgi-permutation (xs outputs))
     (:instance zcf-natp-of-rgi-position
                (x row) (xs inputs))
     (:instance zcf-natp-of-rgi-position
                (x column) (xs kernels))
     (:instance zcf-position-below-rader-size
                (xs inputs) (x row))
     (:instance zcf-position-below-rader-size
                (xs kernels) (x column))
     (:instance zcf-permutation-residue-of-nth
                (xs outputs) (i m))
     (:instance zcf-column-matches-rader-product-iff-difference-position)
     (:instance zcf-cyclic-sum-index
                (n (1- (nfix p)))
                (a (rgi-position row inputs))
                (b (rgi-position column kernels))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-lifted-entry rgi-fourier-entry
       posp natp nfix)))))

(defthm zcf-zero-times
  (equal (* 0 x) 0))

(defthm zcf-zero-row-zero-column-entry
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (+ (rgi-base-entry 0 0)
       (rgi-lifted-entry (1- (nfix p)) m
                         0 0 inputs kernels))
    (rgi-fourier-entry p (nth m outputs) 0 0)))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-input-permutation)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance zcf-position-zero-of-permutation
                (xs inputs))
     (:instance zcf-position-zero-of-permutation
                (xs kernels)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-base-entry rgi-lifted-entry rgi-fourier-entry
       zcf-zero-times mod-of-0-arg1 nfix posp natp)))))

(defthm zcf-zero-row-positive-column-entry
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp column)
        (< column (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (+ (rgi-base-entry 0 column)
       (rgi-lifted-entry (1- (nfix p)) m
                         0 column inputs kernels))
    (rgi-fourier-entry p (nth m outputs) 0 column)))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-input-permutation)
     (:instance zcf-position-zero-of-permutation
                (xs inputs)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-base-entry rgi-lifted-entry rgi-fourier-entry
       zcf-zero-times mod-of-0-arg1 nfix posp natp)))))

(defthm zcf-positive-row-zero-column-entry
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (posp row)
        (< row (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (+ (rgi-base-entry row 0)
       (rgi-lifted-entry (1- (nfix p)) m
                         row 0 inputs kernels))
    (rgi-fourier-entry p (nth m outputs) row 0)))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance rgi-index-certificate-implies-output-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs outputs))
     (:instance zcf-permutation-residue-of-nth
                (xs outputs) (i m))
     (:instance zcf-position-zero-of-permutation
                (xs kernels))
     (:instance zcf-index-relation-product-positive))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-base-entry rgi-lifted-entry rgi-fourier-entry
       nfix posp natp)))))

(defthm zcf-index-certificate-pointwise-compact
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp row)
        (< row (nfix p))
        (natp column)
        (< column (nfix p))
        (natp m)
        (< m (1- (nfix p))))
   (equal
    (+ (rgi-base-entry row column)
       (rgi-lifted-entry (1- (nfix p)) m
                         row column inputs kernels))
    (rgi-fourier-entry p (nth m outputs) row column)))
  :hints
  (("Goal"
    :cases ((equal row 0)
            (equal column 0))
    :use
    ((:instance zcf-zero-row-zero-column-entry)
     (:instance zcf-zero-row-positive-column-entry)
     (:instance zcf-positive-row-zero-column-entry)
     (:instance zcf-positive-row-column-entry))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-base-entry posp natp nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fold the pointwise equality back into the executable compact checkers.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-build-compact-output-rowp-step
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p)))
        (natp column)
        (< column (nfix p))
        (natp count)
        (not (zp count))
        (<= count (nfix p))
        (rgi-compact-output-rowp
         (1- count) column p m (nth m outputs) inputs kernels))
   (rgi-compact-output-rowp
    count column p m (nth m outputs) inputs kernels))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-natp-of-predecessor)
     (:instance rgi-predecessor-below-bound
                (n (nfix p)))
     (:instance zcf-index-certificate-pointwise-compact
                (row (1- count))))
    :expand
    ((rgi-compact-output-rowp
      count column p m (nth m outputs) inputs kernels))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-nfix-when-natp natp)))))

(defthm zcf-build-compact-output-rowp
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p)))
        (natp column)
        (< column (nfix p))
        (natp count)
        (<= count (nfix p)))
   (rgi-compact-output-rowp
    count column p m (nth m outputs) inputs kernels))
  :hints
  (("Goal"
    :induct (rgi-count-induct count)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-count-induct)))
   ("Subgoal *1/2"
    :use ((:instance zcf-build-compact-output-rowp-step))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-predecessor
       rgi-predecessor-not-above-bound)))
   ("Subgoal *1/1"
    :use ((:instance rgi-zp-natural-is-zero))
    :expand
    ((rgi-compact-output-rowp
      0 column p m (nth m outputs) inputs kernels))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zp)))))

(defthm zcf-build-compact-outputp-aux-step
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p)))
        (natp count)
        (not (zp count))
        (<= count (nfix p))
        (rgi-compact-outputp-aux
         (1- count) p m (nth m outputs) inputs kernels))
   (rgi-compact-outputp-aux
    count p m (nth m outputs) inputs kernels))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-natp-of-predecessor)
     (:instance rgi-predecessor-below-bound
                (n (nfix p)))
     (:instance zcf-build-compact-output-rowp
                (count (nfix p))
                (column (1- count))))
    :expand
    ((rgi-compact-outputp-aux
      count p m (nth m outputs) inputs kernels))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-nfix-when-natp natp)))))

(defthm zcf-build-compact-outputp-aux
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p)))
        (natp count)
        (<= count (nfix p)))
   (rgi-compact-outputp-aux
    count p m (nth m outputs) inputs kernels))
  :hints
  (("Goal"
    :induct (rgi-count-induct count)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-count-induct)))
   ("Subgoal *1/2"
    :use ((:instance zcf-build-compact-outputp-aux-step))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-predecessor
       rgi-predecessor-not-above-bound)))
   ("Subgoal *1/1"
    :use ((:instance rgi-zp-natural-is-zero))
    :expand
    ((rgi-compact-outputp-aux
      0 p m (nth m outputs) inputs kernels))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zp)))))

(defthm zcf-index-certificate-implies-compact-output
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp m)
        (< m (1- (nfix p))))
   (rgi-compact-outputp
    p m (nth m outputs) inputs kernels))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-input-permutation)
     (:instance rgi-index-certificate-implies-kernel-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs inputs))
     (:instance zcf-len-of-rgi-permutation
                (xs kernels))
     (:instance zcf-build-compact-outputp-aux
                (count p)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-compact-outputp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Walk the output suffix in lockstep with its small-output index.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zcf-bank-suffix-induct (small-out suffix)
  (declare (xargs :measure (acl2-count suffix)))
  (if (endp suffix)
      (list small-out suffix)
    (zcf-bank-suffix-induct
     (1+ (nfix small-out)) (cdr suffix))))


(defthm zcf-compact-bankp-aux-open
  (implies (consp suffix)
           (equal
            (rgi-compact-bankp-aux
             small-out p suffix inputs kernels)
            (and
             (rgi-compact-outputp
              p (nfix small-out) (car suffix) inputs kernels)
             (rgi-compact-bankp-aux
              (1+ (nfix small-out)) p (cdr suffix)
              inputs kernels))))
  :hints
  (("Goal"
    :expand
    ((rgi-compact-bankp-aux
      small-out p suffix inputs kernels))
    :in-theory (theory 'minimal-theory))))

(defthm zcf-compact-bankp-aux-closed
  (implies (not (consp suffix))
           (rgi-compact-bankp-aux
            small-out p suffix inputs kernels))
  :hints
  (("Goal"
    :expand
    ((rgi-compact-bankp-aux
      small-out p suffix inputs kernels))
    :in-theory (theory 'minimal-theory))))

(defthm zcf-build-compact-bankp-aux-general
  (implies
   (and (rgi-index-certificatep p inputs kernels outputs)
        (natp small-out)
        (<= small-out (1- (nfix p)))
        (equal suffix (nthcdr small-out outputs)))
   (rgi-compact-bankp-aux
    small-out p suffix inputs kernels))
  :hints
  (("Goal"
    :induct (zcf-bank-suffix-induct small-out suffix)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcf-bank-suffix-induct)))
   ("Subgoal *1/2"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-output-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs outputs))
     (:instance consp-of-nthcdr
                (n small-out) (x outputs))
     (:instance car-of-nthcdr
                (i small-out) (x outputs))
     (:instance cdr-of-nthcdr
                (n small-out) (x outputs))
     (:instance zcf-index-certificate-implies-compact-output
                (m small-out))
     (:instance zcf-compact-bankp-aux-open))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(natp nfix)))
   ("Subgoal *1/1"
    :use ((:instance zcf-compact-bankp-aux-closed))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-index-certificate-implies-compact-bank
  (implies
   (rgi-index-certificatep p inputs kernels outputs)
   (rgi-compact-bankp p outputs inputs kernels))
  :hints
  (("Goal"
    :use
    ((:instance zcf-index-certificate-size)
     (:instance rgi-index-certificate-implies-output-permutation)
     (:instance zcf-len-of-rgi-permutation
                (xs outputs))
     (:instance zcf-build-compact-bankp-aux-general
                (small-out 0)
                (suffix outputs)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-compact-bankp nthcdr-of-0 natp)))))

(defthm rgi-generated-index-certificate-implies-compact-bank
  (implies
   (rgi-generated-index-certificatep p generator)
   (rgi-compact-bankp
    p
    (rgi-generated-outputs p generator)
    (rgi-generated-inputs p generator)
    (rgi-generated-kernels p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-index-certificate-implies-compact-bank
                (inputs (rgi-generated-inputs p generator))
                (kernels (rgi-generated-kernels p generator))
                (outputs (rgi-generated-outputs p generator))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-generated-index-certificatep)))))

(defthm rgi-generated-compact-bankp-universal
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rgi-compact-bankp
    p
    (rgi-generated-outputs p generator)
    (rgi-generated-inputs p generator)
    (rgi-generated-kernels p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-generated-index-certificatep-universal)
     (:instance rgi-generated-index-certificate-implies-compact-bank))
    :in-theory (theory 'minimal-theory))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End-to-end generated WFTA: primitive-root orbit to compiled transform.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zcf-generated-primitive-root-wfta-certificate
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rwd-compiled-certifiesp
    p
    (rgi-generated-inputs p generator)
    (rgi-generated-kernels p generator)
    (rgi-generated-outputs p generator)
    (tc-plan-terms (1- (nfix p)))
    (tc-plan-posts (1- (nfix p)))))
  :hints
  (("Goal"
    :use
    ((:instance rgi-generated-index-certificatep-universal)
     (:instance rgi-generated-compact-bankp-universal)
     (:instance zcf-index-certificate-size
                (inputs (rgi-generated-inputs p generator))
                (kernels (rgi-generated-kernels p generator))
                (outputs (rgi-generated-outputs p generator)))
     (:instance urw-generated-wfta-certificate
                (inputs (rgi-generated-inputs p generator))
                (kernels (rgi-generated-kernels p generator))
                (outputs (rgi-generated-outputs p generator))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-generated-index-certificatep)))))

(defthm zcf-generated-primitive-root-wfta-correct
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (qcx-vectorp p xs)
        (qcx-vectorp p table))
   (equal
    (rwd-run
     p
     (rgi-generated-inputs p generator)
     (rgi-generated-kernels p generator)
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p)))
     xs table)
    (rwd-direct-outputs
     (rwd-output-order (rgi-generated-outputs p generator))
     p xs table)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-generated-index-certificatep-universal)
     (:instance rgi-generated-compact-bankp-universal)
     (:instance zcf-index-certificate-size
                (inputs (rgi-generated-inputs p generator))
                (kernels (rgi-generated-kernels p generator))
                (outputs (rgi-generated-outputs p generator)))
     (:instance urw-generated-wfta-correct
                (inputs (rgi-generated-inputs p generator))
                (kernels (rgi-generated-kernels p generator))
                (outputs (rgi-generated-outputs p generator))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-generated-index-certificatep)))))
