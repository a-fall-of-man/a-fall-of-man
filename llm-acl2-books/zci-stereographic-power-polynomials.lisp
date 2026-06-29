; Exact coefficient recurrences for powers of a rational stereographic unit.
; Everything here is finite rational algebra in ordinary ACL2.
(in-package "ACL2")

(include-book "zch-rational-polynomial-sign-bisection")
(include-book "zbb-rational-cyclic-twiddle-system")

(defun rts-poly-shift (p)
  (cons 0 p))

(defun rts-poly-shift2 (p)
  (cons 0 (cons 0 p)))

(defun rts-real-step (a b)
  (tc-poly-add
   (tc-poly-add a (tc-poly-scale -1 (rts-poly-shift2 a)))
   (tc-poly-scale -2 (rts-poly-shift b))))

(defun rts-imag-step (a b)
  (tc-poly-add
   (tc-poly-add b (tc-poly-scale -1 (rts-poly-shift2 b)))
   (tc-poly-scale 2 (rts-poly-shift a))))

(defun rts-power-polynomials (steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons '(1) nil)
    (let* ((previous (rts-power-polynomials (1- steps)))
           (a (car previous))
           (b (cdr previous)))
      (cons (rts-real-step a b)
            (rts-imag-step a b)))))

(defun rts-real-polynomial (steps)
  (car (rts-power-polynomials steps)))

(defun rts-imag-polynomial (steps)
  (cdr (rts-power-polynomials steps)))

(defun rts-unit-numerator (tangent)
  (qcx (- 1 (* tangent tangent))
       (* 2 tangent)))

(defun rts-evaluated-numerator (steps tangent)
  (qcx (tc-poly-eval (rts-real-polynomial steps) tangent)
       (tc-poly-eval (rts-imag-polynomial steps) tangent)))

(defun rts-raw-power (steps tangent)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (qcx-one)
    (qcx-mul (rts-raw-power (1- steps) tangent)
             (rts-unit-numerator tangent))))

(defthm rational-listp-of-rts-poly-shift
  (implies (rational-listp p)
           (rational-listp (rts-poly-shift p)))
  :hints (("Goal" :in-theory (enable rts-poly-shift))))

(defthm rational-listp-of-rts-poly-shift2
  (implies (rational-listp p)
           (rational-listp (rts-poly-shift2 p)))
  :hints (("Goal" :in-theory (enable rts-poly-shift2))))

(defthm rational-listp-of-tc-poly-add
  (implies (and (rational-listp a)
                (rational-listp b))
           (rational-listp (tc-poly-add a b)))
  :hints (("Goal"
           :induct (tc-poly-add a b)
           :in-theory (enable tc-poly-add))))

(defthm rational-listp-of-rts-real-step
  (implies (and (rational-listp a)
                (rational-listp b))
           (rational-listp (rts-real-step a b)))
  :hints (("Goal" :in-theory (enable rts-real-step))))

(defthm rational-listp-of-rts-imag-step
  (implies (and (rational-listp a)
                (rational-listp b))
           (rational-listp (rts-imag-step a b)))
  :hints (("Goal" :in-theory (enable rts-imag-step))))

(defthm rational-listp-of-rts-power-polynomials
  (and (rational-listp (car (rts-power-polynomials steps)))
       (rational-listp (cdr (rts-power-polynomials steps))))
  :hints (("Goal"
           :induct (rts-power-polynomials steps)
           :in-theory (enable rts-power-polynomials))))

(defthm tc-poly-eval-of-rts-poly-shift
  (equal (tc-poly-eval (rts-poly-shift p) x)
         (* x (tc-poly-eval p x)))
  :hints (("Goal" :in-theory (enable rts-poly-shift tc-poly-eval))))

(defthm tc-poly-eval-of-rts-poly-shift2
  (equal (tc-poly-eval (rts-poly-shift2 p) x)
         (* x x (tc-poly-eval p x)))
  :hints (("Goal" :in-theory (enable rts-poly-shift2 tc-poly-eval))))

(defthm tc-poly-eval-of-rts-real-step
  (implies (and (rational-listp a)
                (rational-listp b)
                (rationalp x))
           (equal (tc-poly-eval (rts-real-step a b) x)
                  (- (* (- 1 (* x x)) (tc-poly-eval a x))
                     (* 2 x (tc-poly-eval b x)))))
  :hints (("Goal"
           :use ((:instance tc-poly-eval-of-tc-poly-add
                            (a (tc-poly-add
                                a (tc-poly-scale -1 (rts-poly-shift2 a))))
                            (b (tc-poly-scale -2 (rts-poly-shift b))))
                 (:instance tc-poly-eval-of-tc-poly-add
                            (b (tc-poly-scale -1 (rts-poly-shift2 a))))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c -1) (p (rts-poly-shift2 a)))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c -2) (p (rts-poly-shift b))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-real-step
              tc-poly-eval-of-rts-poly-shift
              tc-poly-eval-of-rts-poly-shift2
              rational-listp-of-rts-poly-shift
              rational-listp-of-rts-poly-shift2
              rational-listp-of-tc-poly-add
              rational-listp-of-tc-poly-scale))
           :nonlinearp t)))

(defthm tc-poly-eval-of-rts-imag-step
  (implies (and (rational-listp a)
                (rational-listp b)
                (rationalp x))
           (equal (tc-poly-eval (rts-imag-step a b) x)
                  (+ (* 2 x (tc-poly-eval a x))
                     (* (- 1 (* x x)) (tc-poly-eval b x)))))
  :hints (("Goal"
           :use ((:instance tc-poly-eval-of-tc-poly-add
                            (a (tc-poly-add
                                b (tc-poly-scale -1 (rts-poly-shift2 b))))
                            (b (tc-poly-scale 2 (rts-poly-shift a))))
                 (:instance tc-poly-eval-of-tc-poly-add
                            (a b)
                            (b (tc-poly-scale -1 (rts-poly-shift2 b))))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c -1) (p (rts-poly-shift2 b)))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c 2) (p (rts-poly-shift a))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-imag-step
              tc-poly-eval-of-rts-poly-shift
              tc-poly-eval-of-rts-poly-shift2
              rational-listp-of-rts-poly-shift
              rational-listp-of-rts-poly-shift2
              rational-listp-of-tc-poly-add
              rational-listp-of-tc-poly-scale))
           :nonlinearp t)))

(defthm qcx-rationalp-of-rts-unit-numerator
  (implies (rationalp tangent)
           (qcx-rationalp (rts-unit-numerator tangent)))
  :hints (("Goal" :in-theory (enable rts-unit-numerator qcx-rationalp qcx))))

(defthm qcx-rationalp-of-rts-raw-power
  (implies (rationalp tangent)
           (qcx-rationalp (rts-raw-power steps tangent)))
  :hints (("Goal"
           :induct (rts-raw-power steps tangent)
           :in-theory (enable rts-raw-power))))

(defthm rts-power-polynomials-when-zp
  (implies (zp steps)
           (equal (rts-power-polynomials steps)
                  (cons '(1) nil)))
  :hints (("Goal"
           :expand ((rts-power-polynomials steps))
           :in-theory (theory 'minimal-theory))))

(defthm rts-power-polynomials-open
  (implies (not (zp steps))
           (equal (rts-power-polynomials steps)
                  (let* ((previous (rts-power-polynomials (1- steps)))
                         (a (car previous))
                         (b (cdr previous)))
                    (cons (rts-real-step a b)
                          (rts-imag-step a b)))))
  :hints (("Goal"
           :expand ((rts-power-polynomials steps))
           :in-theory (theory 'minimal-theory))))

(defthm rts-evaluated-numerator-when-zp
  (implies (zp steps)
           (equal (rts-evaluated-numerator steps tangent)
                  (qcx-one)))
  :hints (("Goal"
           :use ((:instance rts-power-polynomials-when-zp))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rts-evaluated-numerator
              rts-real-polynomial
              rts-imag-polynomial
              tc-poly-eval
              qcx-one qcx car-cons cdr-cons)))))

(defthm rts-qcx-step-algebra
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp tangent))
           (equal
            (qcx (- (* (- 1 (* tangent tangent)) a)
                    (* 2 tangent b))
                 (+ (* 2 tangent a)
                    (* (- 1 (* tangent tangent)) b)))
            (qcx-mul (qcx a b)
                     (rts-unit-numerator tangent))))
  :hints (("Goal"
           :in-theory (e/d (qcx-mul qcx qcx-re qcx-im
                                     rts-unit-numerator)
                            (qcx-mul-commutative
                             normalize-factors-gather-exponents))
           :nonlinearp t)))

(defthm rts-evaluated-numerator-open
  (implies (and (not (zp steps))
                (rationalp tangent))
           (equal (rts-evaluated-numerator steps tangent)
                  (qcx-mul
                   (rts-evaluated-numerator (1- steps) tangent)
                   (rts-unit-numerator tangent))))
  :hints
  (("Goal"
    :use ((:instance rts-power-polynomials-open)
          (:instance rational-listp-of-rts-power-polynomials
                     (steps (1- steps)))
          (:instance tc-poly-eval-of-rts-real-step
                     (a (car (rts-power-polynomials (1- steps))))
                     (b (cdr (rts-power-polynomials (1- steps))))
                     (x tangent))
          (:instance tc-poly-eval-of-rts-imag-step
                     (a (car (rts-power-polynomials (1- steps))))
                     (b (cdr (rts-power-polynomials (1- steps))))
                     (x tangent))
          (:instance rationalp-of-tc-poly-eval
                     (p (car (rts-power-polynomials (1- steps))))
                     (x tangent))
          (:instance rationalp-of-tc-poly-eval
                     (p (cdr (rts-power-polynomials (1- steps))))
                     (x tangent))
          (:instance rts-qcx-step-algebra
                     (a (tc-poly-eval
                         (car (rts-power-polynomials (1- steps))) tangent))
                     (b (tc-poly-eval
                         (cdr (rts-power-polynomials (1- steps))) tangent))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-evaluated-numerator
       rts-real-polynomial
       rts-imag-polynomial
       rts-unit-numerator
       qcx-mul qcx qcx-re qcx-im
       car-cons cdr-cons
       rts-qcx-step-algebra)))))

(defthm rts-raw-power-when-zp
  (implies (zp steps)
           (equal (rts-raw-power steps tangent)
                  (qcx-one)))
  :hints (("Goal"
           :expand ((rts-raw-power steps tangent))
           :in-theory (theory 'minimal-theory))))

(defthm rts-raw-power-open
  (implies (not (zp steps))
           (equal (rts-raw-power steps tangent)
                  (qcx-mul (rts-raw-power (1- steps) tangent)
                           (rts-unit-numerator tangent))))
  :hints (("Goal"
           :expand ((rts-raw-power steps tangent))
           :in-theory (theory 'minimal-theory))))

(defthm rts-evaluated-numerator-equals-raw-power
  (implies (rationalp tangent)
           (equal (rts-evaluated-numerator steps tangent)
                  (rts-raw-power steps tangent)))
  :hints
  (("Goal"
    :induct (rts-raw-power steps tangent)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rts-raw-power)
       rts-evaluated-numerator-when-zp
       rts-evaluated-numerator-open
       rts-raw-power-when-zp
       rts-raw-power-open)))))
