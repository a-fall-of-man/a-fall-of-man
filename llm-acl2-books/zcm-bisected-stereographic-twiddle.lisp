; Epsilon certificates from rational sign bisection for stereographic
; twiddles.  Ordinary ACL2, finite rational arithmetic only.
(in-package "ACL2")

(include-book "zcl-rational-polynomial-secant-bound")
(include-book "zch-rational-polynomial-sign-bisection")

(defthm rts-unit-positive-real-controls-l1-distance
  (implies (and (rationalp re)
                (rationalp im)
                (<= 0 re)
                (equal (+ (* re re) (* im im)) 1))
           (<= (+ (abs (- re 1)) (abs im))
               (* 2 (abs im))))
  :hints (("Goal"
           :cases ((< re 1) (< im 0))
           :in-theory (enable abs)
           :nonlinearp t)))

(defun rts-normalized-real (steps tangent)
  (qcx-re (rts-normalized-polynomial-power steps tangent)))

(defun rts-normalized-imag (steps tangent)
  (qcx-im (rts-normalized-polynomial-power steps tangent)))

(defun rts-bisected-interval (precision n lo hi)
  (rpb-build precision (rts-imag-polynomial n) lo hi))

(defun rts-bisected-lower (precision n lo hi)
  (rpb-lo (rts-bisected-interval precision n lo hi)))

(defun rts-bisected-tangent (precision n lo hi)
  (rpb-hi (rts-bisected-interval precision n lo hi)))

(defun rts-bisected-secant-bound (precision n lo hi radius)
  (let* ((lower (rts-bisected-lower precision n lo hi))
         (upper (rts-bisected-tangent precision n lo hi))
         (poly (rts-imag-polynomial n)))
    (* (abs (- upper lower))
       (rts-poly-abs-bound
        (tc-poly-quotient-linear poly lower)
        radius))))

(defun rts-bisected-closure-bound (precision n lo hi radius)
  (* 2
     (abs (rts-inverse-denominator-power
           n (rts-bisected-tangent precision n lo hi)))
     (rts-bisected-secant-bound precision n lo hi radius)))

(defun rts-bisected-twiddle-certificatep
  (n epsilon precision lo hi radius)
  (let ((tangent (rts-bisected-tangent precision n lo hi)))
    (and (posp n)
         (rationalp epsilon)
         (<= 0 epsilon)
         (rationalp radius)
         (rpb-sign-bracketp
          (rts-imag-polynomial n) (cons lo hi))
         (<= (abs tangent) (abs radius))
         (<= 0 (rts-normalized-real n tangent))
         (<= (rts-bisected-closure-bound
              precision n lo hi radius)
             epsilon)
         (< 0 (rts-table-min-distance
               (rts-proper-power-table
                n (rct-rational-unit nil tangent)))))))

(defthm qcx-rationalp-of-rts-normalized-polynomial-power
  (implies (rationalp tangent)
           (qcx-rationalp
            (rts-normalized-polynomial-power steps tangent)))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-polynomial-power-is-qcx-power)
          (:instance qcx-rationalp-of-rts-qcx-power
                     (seed (rct-rational-unit nil tangent)))
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil)))
    :in-theory (theory 'minimal-theory))))

(defthm rationalp-of-qcx-re-when-qcx-rationalp
  (implies (qcx-rationalp z)
           (rationalp (qcx-re z)))
  :hints (("Goal" :in-theory (enable qcx-rationalp qcx-re)))
  :rule-classes :type-prescription)

(defthm rationalp-of-qcx-im-when-qcx-rationalp
  (implies (qcx-rationalp z)
           (rationalp (qcx-im z)))
  :hints (("Goal" :in-theory (enable qcx-rationalp qcx-im)))
  :rule-classes :type-prescription)

(defthm rationalp-of-rts-normalized-real
  (implies (rationalp tangent)
           (rationalp (rts-normalized-real steps tangent)))
  :hints
  (("Goal"
    :use ((:instance qcx-rationalp-of-rts-normalized-polynomial-power)
          (:instance rationalp-of-qcx-re-when-qcx-rationalp
                     (z (rts-normalized-polynomial-power
                         steps tangent))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-normalized-real))))
  :rule-classes :type-prescription)

(defthm rationalp-of-rts-normalized-imag
  (implies (rationalp tangent)
           (rationalp (rts-normalized-imag steps tangent)))
  :hints
  (("Goal"
    :use ((:instance qcx-rationalp-of-rts-normalized-polynomial-power)
          (:instance rationalp-of-qcx-im-when-qcx-rationalp
                     (z (rts-normalized-polynomial-power
                         steps tangent))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-normalized-imag))))
  :rule-classes :type-prescription)

(defthm rts-normalized-components-have-unit-square
  (implies (rationalp tangent)
           (equal (+ (* (rts-normalized-real steps tangent)
                        (rts-normalized-real steps tangent))
                     (* (rts-normalized-imag steps tangent)
                        (rts-normalized-imag steps tangent)))
                  1))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-polynomial-power-is-advance)
          (:instance qcx-rationalp-of-one)
          (:instance qcx-norm-square-of-rct-advance
                     (current (qcx-one))
                     (seed (rct-rational-unit nil tangent)))
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil))
          (:instance qcx-norm-square-of-rct-rational-unit
                     (other-chart nil)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-real rts-normalized-imag
       qcx-rationalp-of-one qcx-one qcx-norm-square qcx qcx-re qcx-im)))))

(defthm rts-opposite-sign-upper-abs-at-most-difference
  (implies (and (rationalp lower-value)
                (rationalp upper-value)
                (<= lower-value 0)
                (<= 0 upper-value))
           (<= (abs upper-value)
               (abs (- upper-value lower-value))))
  :hints (("Goal"
           :in-theory (enable abs)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rts-sign-bracket-upper-polynomial-bound
  (implies (and (rpb-sign-bracketp poly interval)
                (rationalp radius)
                (<= (abs (rpb-hi interval)) (abs radius)))
           (<= (abs (tc-poly-eval poly (rpb-hi interval)))
               (* (abs (- (rpb-hi interval) (rpb-lo interval)))
                  (rts-poly-abs-bound
                   (tc-poly-quotient-linear
                    poly (rpb-lo interval))
                   radius))))
  :hints
  (("Goal"
    :use ((:instance rationalp-of-tc-poly-eval
                     (p poly) (x (rpb-lo interval)))
          (:instance rationalp-of-tc-poly-eval
                     (p poly) (x (rpb-hi interval)))
          (:instance rts-opposite-sign-upper-abs-at-most-difference
                     (lower-value
                      (tc-poly-eval poly (rpb-lo interval)))
                     (upper-value
                      (tc-poly-eval poly (rpb-hi interval))))
          (:instance rts-polynomial-secant-abs-bound
                     (x (rpb-hi interval))
                     (y (rpb-lo interval))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rpb-sign-bracketp)))))

(defthm rts-bisected-interval-preserves-sign-bracket
  (implies (rpb-sign-bracketp
            (rts-imag-polynomial n) (cons lo hi))
           (rpb-sign-bracketp
            (rts-imag-polynomial n)
            (rts-bisected-interval precision n lo hi)))
  :hints
  (("Goal"
    :use ((:instance rpb-build-preserves-sign-bracket
                     (poly (rts-imag-polynomial n))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-bisected-interval)))))

(defthm rationalp-of-rts-bisected-lower
  (implies (rpb-sign-bracketp
            (rts-imag-polynomial n) (cons lo hi))
           (rationalp (rts-bisected-lower precision n lo hi)))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-interval-preserves-sign-bracket)
          (:instance rpb-sign-bracketp-implies-rationalp-lo
                     (poly (rts-imag-polynomial n))
                     (interval (rts-bisected-interval
                                precision n lo hi))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-bisected-lower)))))

(defthm rationalp-of-rts-bisected-tangent
  (implies (rpb-sign-bracketp
            (rts-imag-polynomial n) (cons lo hi))
           (rationalp (rts-bisected-tangent precision n lo hi)))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-interval-preserves-sign-bracket)
          (:instance rpb-sign-bracketp-implies-rationalp-hi
                     (poly (rts-imag-polynomial n))
                     (interval (rts-bisected-interval
                                precision n lo hi))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-bisected-tangent)))))

(defthm rational-listp-of-rts-imag-polynomial
  (rational-listp (rts-imag-polynomial steps))
  :hints
  (("Goal"
    :use ((:instance rational-listp-of-rts-power-polynomials))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-imag-polynomial)))))

(defthm rts-product-of-nonnegatives-nonnegative
  (implies (and (rationalp a)
                (rationalp b)
                (<= 0 a)
                (<= 0 b))
           (<= 0 (* a b)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm rts-bisected-upper-imag-polynomial-bound
  (implies (and (rpb-sign-bracketp
                 (rts-imag-polynomial n) (cons lo hi))
                (rationalp radius)
                (<= (abs (rts-bisected-tangent precision n lo hi))
                    (abs radius)))
           (<= (abs
                (tc-poly-eval
                 (rts-imag-polynomial n)
                 (rts-bisected-tangent precision n lo hi)))
               (rts-bisected-secant-bound
                precision n lo hi radius)))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-interval-preserves-sign-bracket)
          (:instance rts-sign-bracket-upper-polynomial-bound
                     (poly (rts-imag-polynomial n))
                     (interval (rts-bisected-interval
                                precision n lo hi))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-bisected-lower rts-bisected-tangent
       rts-bisected-secant-bound)))))

(defthm rts-bisected-secant-bound-is-rational
  (implies (and (rpb-sign-bracketp
                 (rts-imag-polynomial n) (cons lo hi))
                (rationalp radius))
           (rationalp (rts-bisected-secant-bound
                       precision n lo hi radius)))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-interval-preserves-sign-bracket)
          (:instance rationalp-of-rts-abs
                     (x (- (rts-bisected-tangent precision n lo hi)
                           (rts-bisected-lower precision n lo hi))))
          (:instance rationalp-of-rts-poly-abs-bound
                     (poly (tc-poly-quotient-linear
                            (rts-imag-polynomial n)
                            (rts-bisected-lower precision n lo hi)))
                     (radius radius))
          (:instance rational-listp-of-tc-poly-quotient-linear
                     (p (rts-imag-polynomial n))
                     (root (rts-bisected-lower precision n lo hi))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-bisected-secant-bound
       rts-bisected-lower rts-bisected-tangent
       rpb-sign-bracketp rts-bisected-interval))))
  :rule-classes :type-prescription)

(defthm rts-bisected-secant-bound-nonnegative
  (implies (and (rpb-sign-bracketp
                 (rts-imag-polynomial n) (cons lo hi))
                (rationalp radius))
           (<= 0 (rts-bisected-secant-bound
                  precision n lo hi radius)))
  :hints
  (("Goal"
    :use ((:instance rational-listp-of-rts-imag-polynomial
                     (steps n))
          (:instance rationalp-of-rts-bisected-lower)
          (:instance rationalp-of-rts-bisected-tangent)
          (:instance rationalp-of-rts-abs
                     (x (- (rts-bisected-tangent precision n lo hi)
                           (rts-bisected-lower precision n lo hi))))
          (:instance rts-abs-nonnegative
                     (x (- (rts-bisected-tangent precision n lo hi)
                           (rts-bisected-lower precision n lo hi))))
          (:instance rational-listp-of-tc-poly-quotient-linear
                     (p (rts-imag-polynomial n))
                     (root (rts-bisected-lower precision n lo hi)))
          (:instance rationalp-of-rts-poly-abs-bound
                     (poly (tc-poly-quotient-linear
                            (rts-imag-polynomial n)
                            (rts-bisected-lower precision n lo hi))))
          (:instance rts-poly-abs-bound-nonnegative
                     (poly (tc-poly-quotient-linear
                            (rts-imag-polynomial n)
                            (rts-bisected-lower precision n lo hi))))
          (:instance rts-product-of-nonnegatives-nonnegative
                     (a (abs
                         (- (rts-bisected-tangent precision n lo hi)
                            (rts-bisected-lower precision n lo hi))))
                     (b (rts-poly-abs-bound
                         (tc-poly-quotient-linear
                          (rts-imag-polynomial n)
                          (rts-bisected-lower precision n lo hi))
                         radius))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-bisected-secant-bound)))))

(defthm rts-normalized-imag-is-scaled-imag-polynomial
  (equal (rts-normalized-imag steps tangent)
         (* (rts-inverse-denominator-power steps tangent)
            (tc-poly-eval (rts-imag-polynomial steps) tangent)))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-polynomial-power-components))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-imag qcx-im-of-qcx)))))

(defthm rts-bisected-normalized-imag-bound
  (implies (and (rpb-sign-bracketp
                 (rts-imag-polynomial n) (cons lo hi))
                (rationalp radius)
                (<= (abs (rts-bisected-tangent precision n lo hi))
                    (abs radius)))
           (<= (abs
                (rts-normalized-imag
                 n (rts-bisected-tangent precision n lo hi)))
               (* (abs
                   (rts-inverse-denominator-power
                    n (rts-bisected-tangent precision n lo hi)))
                  (rts-bisected-secant-bound
                   precision n lo hi radius))))
  :hints
  (("Goal"
    :use ((:instance rational-listp-of-rts-imag-polynomial
                     (steps n))
          (:instance rationalp-of-rts-bisected-tangent)
          (:instance rationalp-of-tc-poly-eval
                     (p (rts-imag-polynomial n))
                     (x (rts-bisected-tangent precision n lo hi)))
          (:instance rts-bisected-upper-imag-polynomial-bound)
          (:instance rts-bisected-secant-bound-is-rational)
          (:instance rts-bisected-secant-bound-nonnegative)
          (:instance rts-abs-product-upper-right
                     (x (rts-inverse-denominator-power
                         n (rts-bisected-tangent precision n lo hi)))
                     (q (tc-poly-eval
                         (rts-imag-polynomial n)
                         (rts-bisected-tangent precision n lo hi)))
                     (bound (rts-bisected-secant-bound
                             precision n lo hi radius)))
          (:instance rationalp-of-rts-inverse-denominator-power
                     (steps n)
                     (tangent (rts-bisected-tangent precision n lo hi))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-imag-is-scaled-imag-polynomial
       rpb-sign-bracketp rts-bisected-tangent
       rts-bisected-interval)))))

(defthm qcx-dist-to-one-as-components
  (equal (qcx-dist z (qcx-one))
         (+ (abs (- (qcx-re z) 1))
            (abs (qcx-im z))))
  :hints
  (("Goal"
    :in-theory
    (e/d (qcx-dist qcx-l1 qcx-sub qcx-add qcx-neg
          qcx-one qcx qcx-re qcx-im)
         (qcx-add-commutative
          qcx-mul-commutative
          normalize-factors-gather-exponents)))))

(defthm rts-positive-real-controls-closure-residual
  (implies (and (rationalp tangent)
                (<= 0 (rts-normalized-real n tangent)))
           (<= (rts-polynomial-closure-residual n tangent)
               (* 2 (abs (rts-normalized-imag n tangent)))))
  :hints
  (("Goal"
    :use ((:instance rts-normalized-components-have-unit-square
                     (steps n))
          (:instance rationalp-of-rts-normalized-real
                     (steps n))
          (:instance rationalp-of-rts-normalized-imag
                     (steps n))
          (:instance rts-unit-positive-real-controls-l1-distance
                     (re (rts-normalized-real n tangent))
                     (im (rts-normalized-imag n tangent)))
          (:instance rts-polynomial-closure-residual-is-distance
                     (steps n))
          (:instance qcx-dist-to-one-as-components
                     (z (rts-normalized-polynomial-power n tangent))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-normalized-real rts-normalized-imag)))))

(defthm rts-bisected-closure-residual-bound
  (implies (and (rpb-sign-bracketp
                 (rts-imag-polynomial n) (cons lo hi))
                (rationalp radius)
                (<= (abs (rts-bisected-tangent precision n lo hi))
                    (abs radius))
                (<= 0 (rts-normalized-real
                       n (rts-bisected-tangent precision n lo hi))))
           (<= (rts-polynomial-closure-residual
                n (rts-bisected-tangent precision n lo hi))
               (rts-bisected-closure-bound
                precision n lo hi radius)))
  :hints
  (("Goal"
    :use ((:instance rationalp-of-rts-bisected-tangent)
          (:instance rts-positive-real-controls-closure-residual
                     (tangent (rts-bisected-tangent
                               precision n lo hi)))
          (:instance rts-bisected-normalized-imag-bound))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-bisected-closure-bound)))))

(defthm rts-bisected-certificate-builds-polynomial-closure
  (implies (rts-bisected-twiddle-certificatep
            n epsilon precision lo hi radius)
           (rts-polynomial-closure-certificatep
            n epsilon
            (rts-bisected-tangent precision n lo hi)))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-interval-preserves-sign-bracket)
          (:instance rts-bisected-closure-residual-bound))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-bisected-twiddle-certificatep
       rts-polynomial-closure-certificatep
       rpb-sign-bracketp
       rts-bisected-tangent rts-bisected-interval)))))

(defthm rts-bisected-certificate-builds-twiddle-system
  (implies (rts-bisected-twiddle-certificatep
            n epsilon precision lo hi radius)
           (rct-twiddle-systemp
            n epsilon
            (rts-generated-separation
             n (rct-rational-unit
                nil (rts-bisected-tangent precision n lo hi)))
            (rct-rational-unit
             nil (rts-bisected-tangent precision n lo hi))
            (rct-twiddle-table
             n nil (rts-bisected-tangent precision n lo hi))))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-certificate-builds-polynomial-closure)
          (:instance rts-polynomial-closure-builds-twiddle-system
                     (tangent (rts-bisected-tangent
                               precision n lo hi))))
    :in-theory (theory 'minimal-theory))))
