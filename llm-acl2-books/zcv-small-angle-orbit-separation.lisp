; Total proper-power separation for the explicit small-angle twiddle.
; Ordinary ACL2: finite rational arithmetic and finite orbit folds only.
(in-package "ACL2")

(include-book "zcu-small-angle-total-twiddle")

(defthm zcv-rationalp-when-natp
  (implies (natp x)
           (rationalp x))
  :hints (("Goal" :in-theory (enable natp))))

(defthm zcv-rationalp-of-two-times-nat
  (implies (natp x)
           (rationalp (* 2 x)))
  :hints (("Goal" :use ((:instance zcv-rationalp-when-natp)))))

(defthm zcv-rationalp-of-eight-times-rational
  (implies (rationalp x)
           (rationalp (* 8 x))))

(defthm zcv-two-times-nat-nonnegative
  (implies (natp x)
           (<= 0 (* 2 x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm zcv-eight-times-positive-rational-nonnegative
  (implies (and (rationalp x)
                (< 0 x))
           (<= 0 (* 8 x)))
  :hints (("Goal" :nonlinearp t)))

(defthm zcv-small-power-distance-at-most-eight-k-tangent
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp k))
           (<= (qcx-dist
                (zcu-power k (zcu-small-seed n epsilon))
                (qcx-one))
               (* 8 k (zcu-small-tangent n epsilon))))
  :hints
  (("Goal"
    :use
    ((:instance zcu-power-distance-linear-bound
                (steps k)
                (seed (zcu-small-seed n epsilon)))
     (:instance qcx-rationalp-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance qcx-norm-square-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcu-power-is-rational
                (steps k)
                (seed (zcu-small-seed n epsilon)))
     (:instance zcu-seed-distance-at-most-four-tangent
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcu-small-tangent-rational)
     (:instance zcu-small-tangent-positive)
     (:instance zcu-small-tangent-less-than-one)
     (:instance rationalp-of-qcx-dist
                (x (zcu-small-seed n epsilon))
                (y (qcx-one)))
     (:instance qcx-rationalp-of-one)
     (:instance zcv-rationalp-of-two-times-nat (x k))
     (:instance zcv-two-times-nat-nonnegative (x k))
     (:instance rts-nonnegative-product-monotone
                (a (* 2 k))
                (x (qcx-dist (zcu-small-seed n epsilon)
                             (qcx-one)))
                (y (* 4 (zcu-small-tangent n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed commutativity-of-* associativity-of-*))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcv-small-power-distance-less-than-one
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp k)
                (<= k n))
           (< (qcx-dist
               (zcu-power k (zcu-small-seed n epsilon))
               (qcx-one))
              1))
  :hints
  (("Goal"
    :use
    ((:instance zcv-small-power-distance-at-most-eight-k-tangent)
     (:instance zcu-small-tangent-rational)
     (:instance zcu-small-tangent-positive)
     (:instance zcu-natp-when-posp)
     (:instance zcv-rationalp-when-natp (x k))
     (:instance zcv-rationalp-when-natp (x n))
     (:instance zcv-rationalp-of-eight-times-rational
                (x (zcu-small-tangent n epsilon)))
     (:instance zcv-eight-times-positive-rational-nonnegative
                (x (zcu-small-tangent n epsilon)))
     (:instance zcu-small-tangent-times-eight-n)
     (:instance rts-nonnegative-product-monotone
                (a (* 8 (zcu-small-tangent n epsilon)))
                (x k)
                (y n)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(posp commutativity-of-* associativity-of-*))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcv-abs-one-minus-small
  (implies (and (rationalp x)
                (< (abs (- x 1)) 1))
           (< 0 x))
  :hints
  (("Goal"
    :cases ((< x 1))
    :in-theory
    (union-theories (theory 'minimal-theory) '(abs))
    :nonlinearp t)))

(defthm zcv-real-difference-at-most-distance
  (implies (qcx-rationalp z)
           (<= (abs (- (qcx-re z) 1))
               (qcx-dist z (qcx-one))))
  :hints
  (("Goal"
    :use ((:instance qcx-dist-to-one-as-components)
          (:instance qcx-l1-nonnegative
                     (z (qcx (qcx-im z) 0))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-l1 qcx qcx-re qcx-im abs qcx-rationalp
       qcx-one car-cons cdr-cons))))
  :rule-classes :linear)

(defthm zcv-distance-less-than-one-implies-positive-real
  (implies (and (qcx-rationalp z)
                (< (qcx-dist z (qcx-one)) 1))
           (< 0 (qcx-re z)))
  :hints
  (("Goal"
    :use ((:instance zcv-real-difference-at-most-distance)
          (:instance zcv-abs-one-minus-small
                     (x (qcx-re z))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-rationalp qcx-re))))
  :rule-classes :linear)

(defthm zcv-small-power-positive-real
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp k)
                (<= k n))
           (< 0 (qcx-re
                 (zcu-power k (zcu-small-seed n epsilon)))))
  :hints
  (("Goal"
    :use ((:instance zcv-small-power-distance-less-than-one)
          (:instance zcu-small-tangent-rational)
          (:instance zcu-power-is-rational
                     (steps k)
                     (seed (zcu-small-seed n epsilon)))
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance zcv-distance-less-than-one-implies-positive-real
                     (z (zcu-power k
                                   (zcu-small-seed n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed))))
  :rule-classes :linear)

(defthm zcv-small-seed-positive-real
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< 0 (qcx-re (zcu-small-seed n epsilon))))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-rational)
          (:instance zcu-small-tangent-positive)
          (:instance zcu-small-tangent-less-than-one)
          (:instance zcu-rational-unit-real
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance rct-unit-denominator-positive
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance zcu-positive-reciprocal
                     (x (+ 1 (* (zcu-small-tangent n epsilon)
                                (zcu-small-tangent n epsilon))))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed rct-unit-denominator))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcv-small-seed-positive-imag
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< 0 (qcx-im (zcu-small-seed n epsilon))))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-rational)
          (:instance zcu-small-tangent-positive)
          (:instance zcu-rational-unit-imag
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance rct-unit-denominator-positive
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance zcu-positive-reciprocal
                     (x (+ 1 (* (zcu-small-tangent n epsilon)
                                (zcu-small-tangent n epsilon))))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed rct-unit-denominator))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcv-imag-of-product-positive
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y)
                (< 0 (qcx-re x))
                (< 0 (qcx-im x))
                (< 0 (qcx-re y))
                (<= 0 (qcx-im y)))
           (< 0 (qcx-im (qcx-mul x y))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-mul qcx qcx-re qcx-im qcx-rationalp
       car-cons cdr-cons))
    :nonlinearp t))
  :rule-classes :linear)

(defun zcv-nat-induct (k)
  (if (zp k)
      nil
    (zcv-nat-induct (1- k))))

(defthm zcv-small-power-imag-nonnegative
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp k)
                (<= k n))
           (<= 0 (qcx-im
                  (zcu-power k (zcu-small-seed n epsilon)))))
  :hints
  (("Goal"
    :induct (zcv-nat-induct k)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction zcv-nat-induct)
       zcv-nat-induct zp natp
       zcu-power rts-qcx-power-when-zp
       qcx-one qcx qcx-im car-cons cdr-cons)))
   ("Subgoal *1/2"
    :use ((:instance zcu-power-successor
                     (k (1- k))
                     (seed (zcu-small-seed n epsilon)))
          (:instance zcu-small-tangent-rational)
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance zcu-natp-of-predecessor
                     (steps k))
          (:instance zcu-power-is-rational
                     (steps (1- k))
                     (seed (zcu-small-seed n epsilon)))
          (:instance zcv-small-seed-positive-real)
          (:instance zcv-small-seed-positive-imag)
          (:instance zcv-small-power-positive-real
                     (k (1- k)))
          (:instance zcv-imag-of-product-positive
                     (x (zcu-small-seed n epsilon))
                     (y (zcu-power (1- k)
                                   (zcu-small-seed n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed
       zcu-natp-of-predecessor
       zcu-successor-of-predecessor
       qcx-mul-commutative)))))

(defthm zcv-small-positive-power-positive-imag
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp k)
                (< k n))
           (< 0 (qcx-im
                 (zcu-power (1+ k)
                            (zcu-small-seed n epsilon)))))
  :hints
  (("Goal"
    :use ((:instance zcu-power-successor
                     (seed (zcu-small-seed n epsilon)))
          (:instance zcu-small-tangent-rational)
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance zcu-power-is-rational
                     (steps k)
                     (seed (zcu-small-seed n epsilon)))
          (:instance zcv-small-seed-positive-real)
          (:instance zcv-small-seed-positive-imag)
          (:instance zcv-small-power-positive-real)
          (:instance zcv-small-power-imag-nonnegative)
          (:instance zcv-imag-of-product-positive
                     (x (zcu-small-seed n epsilon))
                     (y (zcu-power k
                                   (zcu-small-seed n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed qcx-mul-commutative))))
  :rule-classes :linear)

(defthm zcv-positive-imag-implies-positive-distance
  (implies (and (qcx-rationalp z)
                (< 0 (qcx-im z)))
           (< 0 (qcx-dist z (qcx-one))))
  :hints
  (("Goal"
    :use ((:instance qcx-dist-to-one-as-components))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-rationalp qcx-im qcx-re abs)))
  )
  :rule-classes :linear)

(defthm zcv-small-positive-index-positive-distance
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp index)
                (posp index)
                (<= index n))
           (< 0
              (qcx-dist
               (zcu-power index (zcu-small-seed n epsilon))
               (qcx-one))))
  :hints
  (("Goal"
    :use
    ((:instance zcu-natp-of-predecessor (steps index))
     (:instance zcu-successor-of-predecessor (steps index))
     (:instance zcv-small-positive-power-positive-imag
                (k (1- index)))
     (:instance zcu-small-tangent-rational)
     (:instance qcx-rationalp-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcu-power-is-rational
                (steps index)
                (seed (zcu-small-seed n epsilon)))
     (:instance zcv-positive-imag-implies-positive-distance
                (z (zcu-power index
                              (zcu-small-seed n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed natp posp zp))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcv-orbit-step-arithmetic
  (implies (and (natp count)
                (not (zp count))
                (natp index)
                (posp index)
                (<= (+ count index) n))
           (and (natp (1- count))
                (natp (1+ index))
                (posp (1+ index))
                (<= index n)
                (<= (+ (1- count) (1+ index)) n)))
  :hints (("Goal" :in-theory (enable natp posp zp)))
  :rule-classes nil)

(defun zcv-orbit-induct (count index)
  (if (zp count)
      index
    (zcv-orbit-induct (1- count) (1+ index))))

(defthm zcv-small-orbit-separated-aux
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon)
                (natp count)
                (natp index)
                (posp index)
                (<= (+ count index) n))
           (rct-separated-orbitp
            count
            (zcu-power index (zcu-small-seed n epsilon))
            (zcu-small-seed n epsilon)
            0))
  :hints
  (("Goal"
    :induct (zcv-orbit-induct count index)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction zcv-orbit-induct)
       zcv-orbit-induct rct-separated-orbitp zp)))
   ("Subgoal *1/2"
    :use
    ((:instance zcv-orbit-step-arithmetic)
     (:instance zcv-small-positive-index-positive-distance)
     (:instance zcu-power-successor
                (k index)
                (seed (zcu-small-seed n epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-separated-orbitp qcx-mul-commutative)))))

(defthm zcv-small-proper-orbit-separated-at-zero
  (implies (and (< 1 n)
                (integerp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (rct-separated-orbitp
            (1- n)
            (zcu-small-seed n epsilon)
            (zcu-small-seed n epsilon)
            0))
  :hints
  (("Goal"
    :use ((:instance zcv-small-orbit-separated-aux
                     (count (1- n))
                     (index 1))
          (:instance zcu-small-tangent-rational)
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)
                     (tangent (zcu-small-tangent n epsilon)))
          (:instance qcx-mul-left-identity
                     (x (zcu-small-seed n epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-power zcu-small-seed
       rts-qcx-power-open rts-qcx-power-when-zp
       zp posp natp)))))

(defthm zcv-rts-min2-positive
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 x)
                (< 0 y))
           (< 0 (rts-min2 x y)))
  :hints (("Goal" :in-theory (enable rts-min2)))
  :rule-classes :linear)

(defthm zcv-separated-nonempty-table-has-positive-minimum
  (implies (and (consp table)
                (qcx-list-rationalp table)
                (rct-table-separated-from-one-p 0 table))
           (< 0 (rts-table-min-distance table)))
  :hints
  (("Goal"
    :induct (rts-table-min-distance table)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-table-min-distance rts-min2
       rct-table-separated-from-one-p qcx-list-rationalp
       endp)))))

(defthm zcv-proper-power-table-consp
  (implies (and (< 1 n)
                (integerp n))
           (consp (rts-proper-power-table n seed)))
  :hints
  (("Goal"
    :use ((:instance consp-of-rct-power-table-aux
                     (count (1- (nfix n)))
                     (current seed)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-proper-power-table nfix zp)))))

(defthm zcv-small-proper-power-minimum-positive
  (implies (and (< 1 n)
                (integerp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< 0
              (rts-table-min-distance
               (rts-proper-power-table
                n (zcu-small-seed n epsilon)))))
  :hints
  (("Goal"
    :use
    ((:instance zcv-small-proper-orbit-separated-at-zero)
     (:instance rct-separated-table-of-orbit
                (count (1- n))
                (current (zcu-small-seed n epsilon))
                (seed (zcu-small-seed n epsilon))
                (separation 0))
     (:instance zcu-small-tangent-rational)
     (:instance qcx-list-rationalp-of-rts-proper-power-table
                (seed (zcu-small-seed n epsilon)))
     (:instance qcx-rationalp-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcv-proper-power-table-consp
                (seed (zcu-small-seed n epsilon)))
     (:instance zcv-separated-nonempty-table-has-positive-minimum
                (table (rts-proper-power-table
                        n (zcu-small-seed n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-proper-power-table zcu-small-seed nfix posp natp)))))

(defthm zcv-small-closure-error-at-most-epsilon
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (<= (rts-closure-error
                n (zcu-small-tangent n epsilon))
               epsilon))
  :hints
  (("Goal"
    :use ((:instance zcu-small-power-closure-bound)
          (:instance zcu-small-tangent-rational)
          (:instance rts-qcx-power-of-unit-is-advance
                     (steps n)
                     (seed (zcu-small-seed n epsilon)))
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)
                     (tangent (zcu-small-tangent n epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-closure-error zcu-power zcu-small-seed)))))

(defthm zcv-small-angle-generated-parameter-certificate
  (implies (and (< 1 n)
                (integerp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (rts-generated-parameter-certificatep
            n epsilon (zcu-small-tangent n epsilon)))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-rational)
          (:instance zcv-small-closure-error-at-most-epsilon)
          (:instance zcv-small-proper-power-minimum-positive))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-generated-parameter-certificatep
       zcu-small-seed posp nfix)))))

(defthm zcv-small-angle-twiddle-system-correct
  (implies (and (< 1 n)
                (integerp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (rct-twiddle-systemp
            n epsilon
            (rts-generated-separation
             n (zcu-small-seed n epsilon))
            (zcu-small-seed n epsilon)
            (rct-twiddle-table
             n nil (zcu-small-tangent n epsilon))))
  :hints
  (("Goal"
    :use ((:instance zcv-small-angle-generated-parameter-certificate)
          (:instance rts-generated-twiddle-system-correct
                     (tangent (zcu-small-tangent n epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed)))))
