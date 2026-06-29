; Exact normalization and closure certificates for generated rational
; stereographic powers.  Ordinary ACL2, finite rational arithmetic only.
(in-package "ACL2")

(include-book "zcj-generated-stereographic-certificate")

(defun rts-inverse-denominator-power (steps tangent)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      1
    (* (/ (rct-unit-denominator tangent))
       (rts-inverse-denominator-power (1- steps) tangent))))

(defun rts-qcx-power (steps seed)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (qcx-one)
    (qcx-mul (rts-qcx-power (1- steps) seed) seed)))

(defun rts-normalized-polynomial-power (steps tangent)
  (qcx-scale (rts-inverse-denominator-power steps tangent)
             (rts-evaluated-numerator steps tangent)))

(defun rts-polynomial-closure-residual (steps tangent)
  (+ (abs (- (* (rts-inverse-denominator-power steps tangent)
                  (tc-poly-eval (rts-real-polynomial steps) tangent))
               1))
     (abs (* (rts-inverse-denominator-power steps tangent)
             (tc-poly-eval (rts-imag-polynomial steps) tangent)))))

(defun rts-polynomial-closure-certificatep (n epsilon tangent)
  (and (posp n)
       (rationalp epsilon)
       (<= 0 epsilon)
       (rationalp tangent)
       (<= (rts-polynomial-closure-residual n tangent) epsilon)
       (< 0 (rts-table-min-distance
             (rts-proper-power-table
              n (rct-rational-unit nil tangent))))))

(defthm rationalp-of-rts-inverse-denominator-power
  (implies (rationalp tangent)
           (rationalp (rts-inverse-denominator-power steps tangent)))
  :hints (("Goal"
           :induct (rts-inverse-denominator-power steps tangent)
           :in-theory (enable rts-inverse-denominator-power
                              rct-unit-denominator)))
  :rule-classes :type-prescription)

(defthm rts-inverse-denominator-factor-rational
  (implies (rationalp tangent)
           (rationalp (/ (rct-unit-denominator tangent))))
  :hints (("Goal" :in-theory (enable rct-unit-denominator)))
  :rule-classes :type-prescription)

(defthm rts-inverse-denominator-factor-positive
  (implies (rationalp tangent)
           (< 0 (/ (rct-unit-denominator tangent))))
  :hints
  (("Goal"
    :use ((:instance rct-unit-denominator-positive)))))

(defthm rts-positive-rational-product
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 x)
                (< 0 y))
           (< 0 (* x y)))
  :hints (("Goal" :nonlinearp t)))

(defthm rts-inverse-denominator-power-positive
  (implies (rationalp tangent)
           (< 0 (rts-inverse-denominator-power steps tangent)))
  :hints (("Goal"
           :induct (rts-inverse-denominator-power steps tangent)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-inverse-denominator-power)))
          ("Subgoal *1/2"
           :use ((:instance rts-inverse-denominator-factor-rational)
                 (:instance rts-inverse-denominator-factor-positive)
                 (:instance rationalp-of-rts-inverse-denominator-power
                            (steps (1- steps)))
                 (:instance rts-positive-rational-product
                            (x (/ (rct-unit-denominator tangent)))
                            (y (rts-inverse-denominator-power
                                (1- steps) tangent))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(rts-inverse-denominator-power))))
  :rule-classes :linear)

(defthm qcx-rationalp-of-rts-qcx-power
  (implies (qcx-rationalp seed)
           (qcx-rationalp (rts-qcx-power steps seed)))
  :hints (("Goal"
           :induct (rts-qcx-power steps seed)
           :in-theory (enable rts-qcx-power))))

(defthm rts-qcx-power-when-zp
  (implies (zp steps)
           (equal (rts-qcx-power steps seed) (qcx-one)))
  :hints (("Goal"
           :expand ((rts-qcx-power steps seed))
           :in-theory (theory 'minimal-theory))))

(defthm rts-qcx-power-open
  (implies (not (zp steps))
           (equal (rts-qcx-power steps seed)
                  (qcx-mul (rts-qcx-power (1- steps) seed) seed)))
  :hints (("Goal"
           :expand ((rts-qcx-power steps seed))
           :in-theory (theory 'minimal-theory))))

(defthm rct-advance-as-rts-qcx-power
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed))
           (equal (rct-advance steps current seed)
                  (qcx-mul current (rts-qcx-power steps seed))))
  :hints
  (("Goal"
    :induct (rct-advance steps current seed)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rct-advance)
       rct-advance
       rts-qcx-power-when-zp
       rts-qcx-power-open
       qcx-mul-associative
       qcx-mul-commutative
       qcx-mul-right-identity
       qcx-rationalp-of-rts-qcx-power
       qcx-rationalp-of-mul)))))

(defthm rts-qcx-power-of-unit-is-advance
  (implies (qcx-rationalp seed)
           (equal (rct-advance steps (qcx-one) seed)
                  (rts-qcx-power steps seed)))
  :hints
  (("Goal"
    :use ((:instance rct-advance-as-rts-qcx-power
                     (current (qcx-one))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(qcx-rationalp-of-one
                      qcx-mul-left-identity
                      qcx-rationalp-of-rts-qcx-power)))))

(defthm qcx-mul-of-two-scales
  (equal (qcx-mul (qcx-scale a x) (qcx-scale b y))
         (qcx-scale (* a b) (qcx-mul x y)))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(qcx-mul-of-scale-left
              qcx-mul-of-scale-right
              qcx-scale-compose
              |(* y x)|)))))

(defthm rct-rational-unit-nil-is-scaled-numerator
  (equal (rct-rational-unit nil tangent)
         (qcx-scale (/ (rct-unit-denominator tangent))
                    (rts-unit-numerator tangent)))
  :hints (("Goal"
           :in-theory
           (enable rct-rational-unit rts-unit-numerator))))

(defthm rts-normalized-polynomial-power-when-zp
  (implies (zp steps)
           (equal (rts-normalized-polynomial-power steps tangent)
                  (qcx-one)))
  :hints
  (("Goal"
    :use ((:instance rts-evaluated-numerator-when-zp))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-polynomial-power
       rts-inverse-denominator-power
       qcx-scale-one
       qcx-rationalp-of-one)))))

(defthm rts-normalized-polynomial-power-open
  (implies (and (not (zp steps))
                (rationalp tangent))
           (equal (rts-normalized-polynomial-power steps tangent)
                  (qcx-mul
                   (rts-normalized-polynomial-power (1- steps) tangent)
                   (rct-rational-unit nil tangent))))
  :hints
  (("Goal"
    :use ((:instance rts-evaluated-numerator-open)
          (:instance rct-rational-unit-nil-is-scaled-numerator)
          (:instance qcx-mul-of-two-scales
                     (a (rts-inverse-denominator-power (1- steps) tangent))
                     (x (rts-evaluated-numerator (1- steps) tangent))
                     (b (/ (rct-unit-denominator tangent)))
                     (y (rts-unit-numerator tangent))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-polynomial-power
       rts-inverse-denominator-power
       |(* y x)|)))))

(defthm rts-normalized-polynomial-power-is-qcx-power
  (implies (rationalp tangent)
           (equal (rts-normalized-polynomial-power steps tangent)
                  (rts-qcx-power steps
                                 (rct-rational-unit nil tangent))))
  :hints
  (("Goal"
    :induct (rts-qcx-power steps (rct-rational-unit nil tangent))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rts-qcx-power)
       rts-qcx-power-when-zp
       rts-qcx-power-open
       rts-normalized-polynomial-power-when-zp
       rts-normalized-polynomial-power-open)))))

(defthm rts-normalized-polynomial-power-is-advance
  (implies (rationalp tangent)
           (equal (rts-normalized-polynomial-power steps tangent)
                  (rct-advance steps (qcx-one)
                               (rct-rational-unit nil tangent))))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-polynomial-power-is-qcx-power)
          (:instance rts-qcx-power-of-unit-is-advance
                     (seed (rct-rational-unit nil tangent)))
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)))
    :in-theory (theory 'minimal-theory))))

(defthm qcx-dist-to-one-of-components
  (equal (qcx-dist (qcx re im) (qcx-one))
         (+ (abs (- re 1)) (abs im)))
  :hints
  (("Goal"
    :in-theory
    (e/d (qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
          qcx-one qcx qcx-re qcx-im)
         (qcx-add-commutative
          qcx-mul-commutative
          normalize-factors-gather-exponents)))))

(defthm rts-normalized-polynomial-power-components
  (equal (rts-normalized-polynomial-power steps tangent)
         (qcx (* (rts-inverse-denominator-power steps tangent)
                 (tc-poly-eval (rts-real-polynomial steps) tangent))
              (* (rts-inverse-denominator-power steps tangent)
                 (tc-poly-eval (rts-imag-polynomial steps) tangent))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-polynomial-power
       rts-evaluated-numerator
       qcx-scale qcx qcx-re qcx-im
       car-cons cdr-cons)))))

(defthm rts-polynomial-closure-residual-is-distance
  (equal (rts-polynomial-closure-residual steps tangent)
         (qcx-dist
          (rts-normalized-polynomial-power steps tangent)
          (qcx-one)))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-polynomial-power-components)
          (:instance qcx-dist-to-one-of-components
                     (re (* (rts-inverse-denominator-power steps tangent)
                            (tc-poly-eval
                             (rts-real-polynomial steps) tangent)))
                     (im (* (rts-inverse-denominator-power steps tangent)
                            (tc-poly-eval
                             (rts-imag-polynomial steps) tangent)))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-polynomial-closure-residual)))))

(defthm rts-polynomial-closure-residual-is-closure-error
  (implies (rationalp tangent)
           (equal (rts-polynomial-closure-residual n tangent)
                  (rts-closure-error n tangent)))
  :hints
  (("Goal"
    :use ((:instance rts-polynomial-closure-residual-is-distance
                     (steps n))
          (:instance rts-normalized-polynomial-power-is-advance
                     (steps n)))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-closure-error)))))

(defthm rts-polynomial-closure-certificate-correct
  (implies (rts-polynomial-closure-certificatep n epsilon tangent)
           (rts-generated-parameter-certificatep n epsilon tangent))
  :hints
  (("Goal"
    :use ((:instance rts-polynomial-closure-residual-is-closure-error))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-polynomial-closure-certificatep
       rts-generated-parameter-certificatep)))))

(defthm rts-polynomial-closure-builds-twiddle-system
  (implies (rts-polynomial-closure-certificatep n epsilon tangent)
           (rct-twiddle-systemp
            n epsilon
            (rts-generated-separation
             n (rct-rational-unit nil tangent))
            (rct-rational-unit nil tangent)
            (rct-twiddle-table n nil tangent)))
  :hints
  (("Goal"
    :use ((:instance rts-polynomial-closure-certificate-correct)
          (:instance rts-generated-twiddle-system-correct))
    :in-theory (theory 'minimal-theory))))
