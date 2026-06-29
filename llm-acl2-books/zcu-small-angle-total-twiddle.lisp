; A total small-angle rational twiddle construction.
; This book proves totality for the existing closure-plus-separation
; specification without using real numbers, bisection, or ACL2(r).
(in-package "ACL2")

(include-book "zct-primitive-root-search-totality")
(include-book "zaw-rational-cauchy-interest")
(include-book "zcl-rational-polynomial-secant-bound")

(defun zcu-power (steps seed)
  (rts-qcx-power steps seed))

(defun zcu-small-denominator (n epsilon)
  (* 16 (nfix n) (+ 1 epsilon)))

(defun zcu-small-tangent (n epsilon)
  (/ epsilon (zcu-small-denominator n epsilon)))

(defun zcu-small-seed (n epsilon)
  (rct-rational-unit nil (zcu-small-tangent n epsilon)))

(defthm zcu-power-is-rational
  (implies (qcx-rationalp seed)
           (qcx-rationalp (zcu-power steps seed)))
  :hints (("Goal"
           :in-theory (enable zcu-power
                              qcx-rationalp-of-rts-qcx-power))))

(defthm zcu-qcx-norm-square-of-one
  (equal (qcx-norm-square (qcx-one)) 1)
  :hints (("Goal"
           :in-theory (enable qcx-norm-square qcx-one qcx qcx-re qcx-im))))

(defthm zcu-power-has-unit-square
  (implies (and (qcx-rationalp seed)
                (equal (qcx-norm-square seed) 1))
           (equal (qcx-norm-square (zcu-power steps seed)) 1))
  :hints
  (("Goal"
    :use
    ((:instance qcx-norm-square-of-rct-advance
                (current (qcx-one)))
     (:instance rts-qcx-power-of-unit-is-advance)
     (:instance qcx-rationalp-of-one)
     (:instance zcu-qcx-norm-square-of-one))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-power)))))

(defthm zcu-abs-of-negation
  (implies (rationalp x)
           (equal (abs (- x)) (abs x)))
  :hints (("Goal"
           :cases ((< x 0))
           :in-theory (enable abs))))

(defthm zcu-abs-sub-upper-bound
  (implies (and (rationalp x) (rationalp y))
           (<= (abs (- x y)) (+ (abs x) (abs y))))
  :hints
  (("Goal"
    :use ((:instance rts-abs-add-upper-bound (x x) (y (- y)))
          (:instance zcu-abs-of-negation (x y)))
    :in-theory (theory 'minimal-theory)))
  :rule-classes :linear)

(defthm zcu-four-products-factor
  (equal (+ (* a c) (* b d) (* a d) (* b c))
         (* (+ a b) (+ c d))))

(defthm zcu-two-by-two-abs-product-bound
  (implies (and (rationalp a) (rationalp b)
                (rationalp c) (rationalp d))
           (<= (+ (abs (- (* a c) (* b d)))
                  (abs (+ (* a d) (* b c))))
               (* (+ (abs a) (abs b))
                  (+ (abs c) (abs d)))))
  :hints
  (("Goal"
    :use ((:instance zcu-abs-sub-upper-bound
                     (x (* a c)) (y (* b d)))
          (:instance rts-abs-add-upper-bound
                     (x (* a d)) (y (* b c)))
          (:instance rts-abs-product (x a) (y c))
          (:instance rts-abs-product (x b) (y d))
          (:instance rts-abs-product (x a) (y d))
          (:instance rts-abs-product (x b) (y c))
          (:instance zcu-four-products-factor
                     (a (abs a)) (b (abs b))
                     (c (abs c)) (d (abs d))))
    :in-theory (theory 'minimal-theory))))

(defthm zcu-qcx-l1-of-mul-upper
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (<= (qcx-l1 (qcx-mul x y))
               (* (qcx-l1 x) (qcx-l1 y))))
  :hints
  (("Goal"
    :use ((:instance zcu-two-by-two-abs-product-bound
                     (a (qcx-re x)) (b (qcx-im x))
                     (c (qcx-re y)) (d (qcx-im y))))
    :in-theory
    (e/d (qcx-l1 qcx-mul qcx-rationalp qcx qcx-re qcx-im)
         (abs normalize-factors-gather-exponents)))))

(defthm zcu-square-nonnegative
  (implies (rationalp x)
           (<= 0 (* x x)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-unit-coordinate-abs-at-most-one
  (implies (and (rationalp x)
                (rationalp y)
                (equal (+ (* x x) (* y y)) 1))
           (<= (abs x) 1))
  :hints
  (("Goal"
    :use ((:instance zcu-square-nonnegative (x y)))
    :cases ((< x 0))
    :in-theory (union-theories (theory 'minimal-theory) '(abs))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-unit-l1-scalar-bound
  (implies (and (rationalp x)
                (rationalp y)
                (equal (+ (* x x) (* y y)) 1))
           (<= (+ (abs x) (abs y)) 2))
  :hints
  (("Goal"
    :use ((:instance zcu-unit-coordinate-abs-at-most-one)
          (:instance zcu-unit-coordinate-abs-at-most-one
                     (x y) (y x)))
    :in-theory (theory 'minimal-theory))))

(defthm zcu-rationalp-of-qcx-l1
  (implies (qcx-rationalp z)
           (rationalp (qcx-l1 z)))
  :hints
  (("Goal"
    :in-theory
    (enable qcx-l1 qcx-rationalp qcx-re qcx-im
            rationalp-of-rts-abs))))

(defthm zcu-unit-square-implies-l1-at-most-two
  (implies (and (qcx-rationalp z)
                (equal (qcx-norm-square z) 1))
           (<= (qcx-l1 z) 2))
  :hints
  (("Goal"
    :use ((:instance zcu-unit-l1-scalar-bound
                     (x (qcx-re z)) (y (qcx-im z))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-l1 qcx-norm-square qcx-rationalp qcx-re qcx-im))))
  :rule-classes :linear)

(defthm zcu-qcx-rationalp-of-sub
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y))
           (qcx-rationalp (qcx-sub x y)))
  :hints
  (("Goal"
    :in-theory
    (enable qcx-sub qcx-add qcx-neg qcx-rationalp qcx qcx-re qcx-im))))

(defthm zcu-ring-real-sub-product
  (equal (+ (+ (* a c) (- (* b d)))
            (- (+ (* e c) (- (* f d)))))
         (+ (* (+ a (- e)) c)
            (- (* (+ b (- f)) d))))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :nonlinearp t)))

(defthm zcu-ring-im-sub-product
  (equal (+ (+ (* a d) (* b c))
            (- (+ (* e d) (* f c))))
         (+ (* (+ a (- e)) d)
            (* (+ b (- f)) c)))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :nonlinearp t)))

(defthm zcu-mul-sub-identity
  (equal (qcx-sub (qcx-mul x z) (qcx-mul y z))
         (qcx-mul (qcx-sub x y) z))
  :hints
  (("Goal"
    :use
    ((:instance zcu-ring-real-sub-product
                (a (qcx-re x)) (b (qcx-im x))
                (c (qcx-re z)) (d (qcx-im z))
                (e (qcx-re y)) (f (qcx-im y)))
     (:instance zcu-ring-im-sub-product
                (a (qcx-re x)) (b (qcx-im x))
                (c (qcx-re z)) (d (qcx-im z))
                (e (qcx-re y)) (f (qcx-im y))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-sub qcx-add qcx-neg qcx-mul qcx qcx-re qcx-im
       car-cons cdr-cons)))))

(defthm zcu-qcx-mul-right-distance-upper
  (implies (and (qcx-rationalp x)
                (qcx-rationalp y)
                (qcx-rationalp z))
           (<= (qcx-dist (qcx-mul x z) (qcx-mul y z))
               (* (qcx-dist x y) (qcx-l1 z))))
  :hints
  (("Goal"
    :use ((:instance zcu-qcx-l1-of-mul-upper
                     (x (qcx-sub x y)) (y z))
          (:instance zcu-qcx-rationalp-of-sub))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-dist zcu-mul-sub-identity)))))

(defthm zcu-not-zp-of-one-plus-nat
  (implies (natp k)
           (not (zp (1+ k))))
  :hints (("Goal" :in-theory (enable zp))))

(defthm zcu-one-minus-one-plus-nat
  (implies (natp k)
           (equal (1- (1+ k)) k)))

(defthm zcu-power-successor
  (implies (natp k)
           (equal (zcu-power (1+ k) seed)
                  (qcx-mul seed (zcu-power k seed))))
  :hints
  (("Goal"
    :use ((:instance rts-qcx-power-open
                     (steps (1+ k))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-power qcx-mul-commutative
       zcu-not-zp-of-one-plus-nat
       zcu-one-minus-one-plus-nat)))))

(defthm zcu-power-step-distance
  (implies (and (natp k)
                (qcx-rationalp seed)
                (equal (qcx-norm-square seed) 1))
           (<= (qcx-dist (zcu-power (1+ k) seed) (qcx-one))
               (+ (qcx-dist (zcu-power k seed) (qcx-one))
                  (* 2 (qcx-dist seed (qcx-one))))))
  :hints
  (("Goal"
    :use
    ((:instance qcx-dist-triangle
                (a (zcu-power (1+ k) seed))
                (b (zcu-power k seed))
                (c (qcx-one)))
     (:instance zcu-qcx-mul-right-distance-upper
                (x seed) (y (qcx-one))
                (z (zcu-power k seed)))
     (:instance zcu-power-is-rational
                (steps k))
     (:instance zcu-power-is-rational
                (steps (1+ k)))
     (:instance zcu-power-has-unit-square
                (steps k))
     (:instance zcu-unit-square-implies-l1-at-most-two
                (z (zcu-power k seed)))
     (:instance qcx-rationalp-of-one)
     (:instance rationalp-of-qcx-dist
                (x seed) (y (qcx-one)))
     (:instance qcx-dist-nonnegative
                (x seed) (y (qcx-one)))
     (:instance zcu-rationalp-of-qcx-l1
                (z (zcu-power k seed)))
     (:instance rts-nonnegative-product-monotone
                (a (qcx-dist seed (qcx-one)))
                (x (qcx-l1 (zcu-power k seed)))
                (y 2)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-power-successor qcx-mul-left-identity
       commutativity-of-*))))
  )

(defthm zcu-natp-of-predecessor
  (implies (and (natp steps)
                (not (zp steps)))
           (natp (1- steps)))
  :hints (("Goal" :in-theory (enable natp zp))))

(defthm zcu-successor-of-predecessor
  (implies (and (natp steps)
                (not (zp steps)))
           (equal (1+ (1- steps)) steps))
  :hints (("Goal" :in-theory (enable natp zp))))

(defthm zcu-power-distance-linear-bound
  (implies (and (natp steps)
                (qcx-rationalp seed)
                (equal (qcx-norm-square seed) 1))
           (<= (qcx-dist (zcu-power steps seed) (qcx-one))
               (* 2 steps (qcx-dist seed (qcx-one)))))
  :hints
  (("Goal"
    :induct (rts-qcx-power steps seed)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rts-qcx-power)
       zcu-power rts-qcx-power-when-zp rts-qcx-power-open
       qcx-dist qcx-sub qcx-add qcx-neg qcx-l1
       qcx-one qcx qcx-re qcx-im abs zp natp)))
   ("Subgoal *1/2"
    :use ((:instance zcu-power-step-distance
                     (k (1- steps)))
          (:instance qcx-dist-nonnegative
                     (x seed) (y (qcx-one))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-natp-of-predecessor
       zcu-successor-of-predecessor
       zcu-one-minus-one-plus-nat
       commutativity-of-*))
    :nonlinearp t)))

(defthm zcu-small-denominator-rational
  (implies (rationalp epsilon)
           (rationalp (zcu-small-denominator n epsilon)))
  :hints (("Goal"
           :in-theory
           (enable zcu-small-denominator)))
  :rule-classes :type-prescription)

(defthm zcu-small-denominator-positive
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< 0 (zcu-small-denominator n epsilon)))
  :hints (("Goal"
           :in-theory
           (e/d (zcu-small-denominator posp)
                (normalize-factors-gather-exponents))
           :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-small-tangent-rational
  (implies (and (posp n)
                (rationalp epsilon))
           (rationalp (zcu-small-tangent n epsilon)))
  :hints (("Goal"
           :in-theory
           (enable zcu-small-tangent
                   zcu-small-denominator-rational)))
  :rule-classes :type-prescription)

(defthm zcu-positive-reciprocal
  (implies (and (rationalp x)
                (< 0 x))
           (< 0 (/ x)))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(|(< 0 (/ x))|))))
  :rule-classes :linear)

(defthm zcu-small-tangent-positive
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< 0 (zcu-small-tangent n epsilon)))
  :hints
  (("Goal"
    :use ((:instance zcu-small-denominator-positive)
          (:instance zcu-small-denominator-rational)
          (:instance zcu-positive-reciprocal
                     (x (zcu-small-denominator n epsilon)))
          (:instance rts-positive-rational-product
                     (x epsilon)
                     (y (/ (zcu-small-denominator n epsilon)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-tangent))))
  :rule-classes :linear)

(defthm zcu-small-tangent-normalization
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (equal (* (zcu-small-denominator n epsilon)
                     (zcu-small-tangent n epsilon))
                  epsilon))
  :hints
  (("Goal"
    :use ((:instance zcu-small-denominator-positive)
          (:instance zcu-small-denominator-rational)
          (:instance tc-reciprocal-times-nonzero-rational
                     (x (zcu-small-denominator n epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-tangent commutativity-of-*
       associativity-of-*))
    :nonlinearp t)))

(defthm zcu-small-tangent-times-eight-n
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< (* 8 n (zcu-small-tangent n epsilon))
              1))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-normalization)
          (:instance zcu-small-tangent-positive))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-denominator posp nfix))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-small-tangent-times-eight-n-at-most-epsilon
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (<= (* 8 n (zcu-small-tangent n epsilon))
               epsilon))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-normalization)
          (:instance zcu-small-tangent-positive))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-denominator posp nfix))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-small-tangent-less-than-one
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (< (zcu-small-tangent n epsilon) 1))
  :hints
  (("Goal"
    :use ((:instance zcu-small-tangent-times-eight-n)
          (:instance zcu-small-tangent-positive))
    :in-theory
    (union-theories (theory 'minimal-theory) '(posp))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-unit-denominator-rational
  (implies (rationalp tangent)
           (rationalp (+ 1 (* tangent tangent))))
  :rule-classes :type-prescription)

(defthm zcu-unit-denominator-reciprocal-cancel
  (implies (rationalp tangent)
           (equal (* (+ 1 (* tangent tangent))
                     (/ (+ 1 (* tangent tangent))))
                  1))
  :hints
  (("Goal"
    :use ((:instance rct-unit-denominator-positive)
          (:instance tc-reciprocal-times-nonzero-rational
                     (x (+ 1 (* tangent tangent)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-unit-denominator commutativity-of-*)))))

(defthm zcu-unit-real-difference
  (implies (rationalp tangent)
           (equal (- (* (/ (+ 1 (* tangent tangent)))
                        (- 1 (* tangent tangent)))
                     1)
                  (* -2 tangent tangent
                     (/ (+ 1 (* tangent tangent))))))
  :hints
  (("Goal"
    :use ((:instance zcu-unit-denominator-reciprocal-cancel))
    :in-theory (theory 'minimal-theory)
    :nonlinearp t)))

(defthm zcu-rational-unit-real
  (equal (qcx-re (rct-rational-unit nil tangent))
         (* (/ (+ 1 (* tangent tangent)))
            (- 1 (* tangent tangent))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-rational-unit rct-unit-denominator
       qcx-scale qcx qcx-re car-cons cdr-cons)))))

(defthm zcu-rational-unit-imag
  (equal (qcx-im (rct-rational-unit nil tangent))
         (* (/ (+ 1 (* tangent tangent)))
            (* 2 tangent)))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-rational-unit rct-unit-denominator
       qcx-scale qcx qcx-im car-cons cdr-cons)))))

(defthm zcu-unit-real-difference-abs
  (implies (and (rationalp tangent)
                (<= 0 tangent))
           (equal (abs (* -2 tangent tangent
                          (/ (+ 1 (* tangent tangent)))))
                  (* 2 tangent tangent
                     (/ (+ 1 (* tangent tangent))))))
  :hints
  (("Goal"
    :use ((:instance rct-unit-denominator-positive)
          (:instance zcu-unit-denominator-rational)
          (:instance zcu-positive-reciprocal
                     (x (+ 1 (* tangent tangent)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-unit-denominator abs))
    :nonlinearp t)))

(defthm zcu-unit-imag-abs
  (implies (and (rationalp tangent)
                (<= 0 tangent))
           (equal (abs (* (/ (+ 1 (* tangent tangent)))
                          (* 2 tangent)))
                  (* 2 tangent
                     (/ (+ 1 (* tangent tangent))))))
  :hints
  (("Goal"
    :use ((:instance rct-unit-denominator-positive)
          (:instance zcu-unit-denominator-rational)
          (:instance zcu-positive-reciprocal
                     (x (+ 1 (* tangent tangent)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-unit-denominator abs))
    :nonlinearp t)))

(defthm zcu-seed-distance-exact
  (implies (and (rationalp tangent)
                (<= 0 tangent))
           (equal (qcx-dist (rct-rational-unit nil tangent) (qcx-one))
                  (/ (+ (* 2 tangent tangent)
                        (* 2 tangent))
                     (+ 1 (* tangent tangent)))))
  :hints
  (("Goal"
    :use ((:instance qcx-dist-to-one-as-components
                     (z (rct-rational-unit nil tangent)))
          (:instance zcu-unit-real-difference)
          (:instance zcu-rational-unit-real)
          (:instance zcu-rational-unit-imag)
          (:instance zcu-unit-real-difference-abs)
          (:instance zcu-unit-imag-abs))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(qcx-one qcx qcx-re qcx-im car-cons cdr-cons))
    :nonlinearp t)))

(defthm zcu-seed-distance-at-most-four-tangent
  (implies (and (rationalp tangent)
                (<= 0 tangent)
                (<= tangent 1))
           (<= (qcx-dist (rct-rational-unit nil tangent) (qcx-one))
               (* 4 tangent)))
  :hints
  (("Goal"
    :use ((:instance zcu-seed-distance-exact)
          (:instance zcu-unit-denominator-reciprocal-cancel)
          (:instance rct-unit-denominator-positive)
          (:instance zcu-unit-denominator-rational)
          (:instance zcu-positive-reciprocal
                     (x (+ 1 (* tangent tangent)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-unit-denominator))
    :nonlinearp t))
  :rule-classes :linear)

(defthm zcu-natp-when-posp
  (implies (posp n)
           (natp n))
  :hints (("Goal" :in-theory (enable posp natp)))
  :rule-classes :forward-chaining)

(defthm zcu-small-power-closure-bound
  (implies (and (posp n)
                (rationalp epsilon)
                (< 0 epsilon))
           (<= (qcx-dist
                (zcu-power n (zcu-small-seed n epsilon))
                (qcx-one))
               epsilon))
  :hints
  (("Goal"
    :use
    ((:instance zcu-natp-when-posp)
     (:instance zcu-power-distance-linear-bound
                (steps n)
                (seed (zcu-small-seed n epsilon)))
     (:instance qcx-rationalp-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance qcx-norm-square-of-rct-rational-unit
                (other-chart nil)
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcu-seed-distance-at-most-four-tangent
                (tangent (zcu-small-tangent n epsilon)))
     (:instance zcu-small-tangent-rational)
     (:instance zcu-small-tangent-positive)
     (:instance zcu-small-tangent-less-than-one)
     (:instance zcu-small-tangent-times-eight-n-at-most-epsilon))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcu-small-seed posp nfix))
    :nonlinearp t)))
