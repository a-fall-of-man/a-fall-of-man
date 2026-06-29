; Finite rational sign-bracket bisection for polynomial roots.
;
; Ordinary ACL2 contains no appeal to a completed real root.  A nested family
; of rational intervals, each carrying opposite polynomial signs and an exact
; dyadic width, is the algebraic object.

(in-package "ACL2")

(include-book "zbn-rational-polynomial-root-bound")
(include-book "zaz-rational-unit-square-root")

(defun rpb-lo (interval)
  (if (consp interval) (car interval) 0))

(defun rpb-hi (interval)
  (if (consp interval) (cdr interval) 0))

(defun rpb-width (interval)
  (- (rpb-hi interval) (rpb-lo interval)))

(defun rpb-midpoint (interval)
  (/ (+ (rpb-lo interval) (rpb-hi interval)) 2))

(defun rpb-sign-bracketp (poly interval)
  (and (rational-listp poly)
       (rationalp (rpb-lo interval))
       (rationalp (rpb-hi interval))
       (<= (rpb-lo interval) (rpb-hi interval))
       (<= (tc-poly-eval poly (rpb-lo interval)) 0)
       (<= 0 (tc-poly-eval poly (rpb-hi interval)))))

(defun rpb-step (poly interval)
  (let ((mid (rpb-midpoint interval)))
    (if (<= (tc-poly-eval poly mid) 0)
        (cons mid (rpb-hi interval))
      (cons (rpb-lo interval) mid))))

(defun rpb-iterate (precision poly interval)
  (declare (xargs :measure (nfix precision)))
  (if (zp precision)
      interval
    (rpb-iterate (1- precision) poly (rpb-step poly interval))))

(defun rpb-build (precision poly lo hi)
  (rpb-iterate precision poly (cons lo hi)))

(defthm rpb-sign-bracketp-implies-rationalp-lo
  (implies (rpb-sign-bracketp poly interval)
           (rationalp (rpb-lo interval)))
  :hints (("Goal" :in-theory (enable rpb-sign-bracketp))))

(defthm rpb-sign-bracketp-implies-rationalp-hi
  (implies (rpb-sign-bracketp poly interval)
           (rationalp (rpb-hi interval)))
  :hints (("Goal" :in-theory (enable rpb-sign-bracketp))))

(defthm rpb-sign-bracketp-implies-ordered
  (implies (rpb-sign-bracketp poly interval)
           (<= (rpb-lo interval) (rpb-hi interval)))
  :hints (("Goal" :in-theory (enable rpb-sign-bracketp)))
  :rule-classes :linear)

(defthm rationalp-of-rpb-midpoint
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval)))
           (rationalp (rpb-midpoint interval)))
  :hints (("Goal" :in-theory (enable rpb-midpoint)))
  :rule-classes :type-prescription)

(defthm rpb-lo-at-most-midpoint
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval))
                (<= (rpb-lo interval) (rpb-hi interval)))
           (<= (rpb-lo interval) (rpb-midpoint interval)))
  :hints (("Goal" :in-theory (enable rpb-midpoint)))
  :rule-classes :linear)

(defthm rpb-midpoint-at-most-hi
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval))
                (<= (rpb-lo interval) (rpb-hi interval)))
           (<= (rpb-midpoint interval) (rpb-hi interval)))
  :hints (("Goal" :in-theory (enable rpb-midpoint)))
  :rule-classes :linear)

(defthm rpb-width-of-step
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval)))
           (equal (rpb-width (rpb-step poly interval))
                  (/ (rpb-width interval) 2)))
  :hints (("Goal"
           :in-theory (enable rpb-step rpb-width rpb-midpoint
                              rpb-lo rpb-hi))))

(defthm rpb-step-when-mid-nonpositive
  (implies (<= (tc-poly-eval poly (rpb-midpoint interval)) 0)
           (equal (rpb-step poly interval)
                  (cons (rpb-midpoint interval) (rpb-hi interval))))
  :hints (("Goal" :in-theory (enable rpb-step))))

(defthm rpb-step-when-mid-positive
  (implies (not (<= (tc-poly-eval poly (rpb-midpoint interval)) 0))
           (equal (rpb-step poly interval)
                  (cons (rpb-lo interval) (rpb-midpoint interval))))
  :hints (("Goal" :in-theory (enable rpb-step))))

(defthm rpb-sign-bracketp-of-step-nonpositive
  (implies (and (rpb-sign-bracketp poly interval)
                (<= (tc-poly-eval poly (rpb-midpoint interval)) 0))
           (rpb-sign-bracketp poly (rpb-step poly interval)))
  :hints (("Goal"
           :use ((:instance rpb-step-when-mid-nonpositive)
                 (:instance rationalp-of-rpb-midpoint)
                 (:instance rpb-midpoint-at-most-hi)
                 (:instance rpb-sign-bracketp-implies-rationalp-lo)
                 (:instance rpb-sign-bracketp-implies-rationalp-hi)
                 (:instance rpb-sign-bracketp-implies-ordered))
           :in-theory
           (union-theories
            '(rpb-sign-bracketp rpb-step rpb-midpoint rpb-lo rpb-hi
              car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm rpb-sign-bracketp-of-step-positive
  (implies (and (rpb-sign-bracketp poly interval)
                (not (<= (tc-poly-eval poly (rpb-midpoint interval)) 0)))
           (rpb-sign-bracketp poly (rpb-step poly interval)))
  :hints (("Goal"
           :use ((:instance rpb-step-when-mid-positive)
                 (:instance rationalp-of-rpb-midpoint)
                 (:instance rationalp-of-tc-poly-eval
                            (p poly)
                            (x (rpb-midpoint interval)))
                 (:instance rpb-lo-at-most-midpoint)
                 (:instance rpb-sign-bracketp-implies-rationalp-lo)
                 (:instance rpb-sign-bracketp-implies-rationalp-hi)
                 (:instance rpb-sign-bracketp-implies-ordered))
           :in-theory
           (union-theories
            '(rpb-sign-bracketp rpb-step rpb-midpoint rpb-lo rpb-hi
              car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm rpb-sign-bracketp-of-step
  (implies (rpb-sign-bracketp poly interval)
           (rpb-sign-bracketp poly (rpb-step poly interval)))
  :hints (("Goal"
           :cases ((<= (tc-poly-eval poly (rpb-midpoint interval)) 0))
           :use ((:instance rpb-sign-bracketp-of-step-nonpositive)
                 (:instance rpb-sign-bracketp-of-step-positive))
           :in-theory (theory 'minimal-theory))))

(defthm rpb-step-is-contained-nonpositive
  (implies (and (rpb-sign-bracketp poly interval)
                (<= (tc-poly-eval poly (rpb-midpoint interval)) 0))
           (and (<= (rpb-lo interval)
                    (rpb-lo (rpb-step poly interval)))
                (<= (rpb-hi (rpb-step poly interval))
                    (rpb-hi interval))))
  :hints (("Goal"
           :use ((:instance rpb-step-when-mid-nonpositive)
                 (:instance rpb-lo-at-most-midpoint)
                 (:instance rpb-sign-bracketp-implies-rationalp-lo)
                 (:instance rpb-sign-bracketp-implies-rationalp-hi)
                 (:instance rpb-sign-bracketp-implies-ordered))
           :in-theory
           (union-theories
            '(rpb-lo rpb-hi car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm rpb-step-is-contained-positive
  (implies (and (rpb-sign-bracketp poly interval)
                (not (<= (tc-poly-eval poly (rpb-midpoint interval)) 0)))
           (and (<= (rpb-lo interval)
                    (rpb-lo (rpb-step poly interval)))
                (<= (rpb-hi (rpb-step poly interval))
                    (rpb-hi interval))))
  :hints (("Goal"
           :use ((:instance rpb-step-when-mid-positive)
                 (:instance rpb-midpoint-at-most-hi)
                 (:instance rpb-sign-bracketp-implies-rationalp-lo)
                 (:instance rpb-sign-bracketp-implies-rationalp-hi)
                 (:instance rpb-sign-bracketp-implies-ordered))
           :in-theory
           (union-theories
            '(rpb-lo rpb-hi car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm rpb-step-is-contained
  (implies (rpb-sign-bracketp poly interval)
           (and (<= (rpb-lo interval)
                    (rpb-lo (rpb-step poly interval)))
                (<= (rpb-hi (rpb-step poly interval))
                    (rpb-hi interval))))
  :hints (("Goal"
           :cases ((<= (tc-poly-eval poly (rpb-midpoint interval)) 0))
           :use ((:instance rpb-step-is-contained-nonpositive)
                 (:instance rpb-step-is-contained-positive))
           :in-theory (theory 'minimal-theory))))

(defthm rationalp-of-rpb-lo-of-step
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval)))
           (rationalp (rpb-lo (rpb-step poly interval))))
  :hints (("Goal"
           :in-theory (enable rpb-step rpb-midpoint rpb-lo rpb-hi))))

(defthm rationalp-of-rpb-hi-of-step
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval)))
           (rationalp (rpb-hi (rpb-step poly interval))))
  :hints (("Goal"
           :in-theory (enable rpb-step rpb-midpoint rpb-lo rpb-hi))))

(defthm rpb-sign-bracketp-of-iterate
  (implies (rpb-sign-bracketp poly interval)
           (rpb-sign-bracketp
            poly (rpb-iterate precision poly interval)))
  :hints (("Goal"
           :induct (rpb-iterate precision poly interval)
           :in-theory
           (union-theories
            '(rpb-iterate)
            (theory 'minimal-theory)))
          ("Subgoal *1/2"
           :use ((:instance rpb-sign-bracketp-of-step))
           :expand ((rpb-iterate precision poly interval))
           :in-theory (theory 'minimal-theory))))

(defun rpb-rational-intervalp (interval)
  (and (rationalp (rpb-lo interval))
       (rationalp (rpb-hi interval))))

(defthm rpb-rational-intervalp-of-step
  (implies (rpb-rational-intervalp interval)
           (rpb-rational-intervalp (rpb-step poly interval)))
  :hints (("Goal"
           :use ((:instance rationalp-of-rpb-lo-of-step)
                 (:instance rationalp-of-rpb-hi-of-step))
           :in-theory (enable rpb-rational-intervalp))))

(defthm rpb-iterate-width-invariant
  (implies (rpb-rational-intervalp interval)
           (equal (rpb-width (rpb-iterate precision poly interval))
                  (* (rusqrt-dyadic-width precision)
                     (rpb-width interval))))
  :hints (("Goal"
           :induct (rpb-iterate precision poly interval)
           :in-theory
           (e/d (rpb-iterate rusqrt-dyadic-width)
                (rpb-step rpb-midpoint rpb-width
                 rpb-step-when-mid-nonpositive
                 rpb-step-when-mid-positive
                 tc-poly-eval)))
          ("Subgoal *1/2"
           :use ((:instance rpb-rational-intervalp-of-step)
                 (:instance rpb-width-of-step))
           :expand ((rpb-iterate precision poly interval)
                    (rusqrt-dyadic-width precision))
           :in-theory
           (disable rpb-step rpb-midpoint rpb-width
                    rpb-step-when-mid-nonpositive
                    rpb-step-when-mid-positive
                    tc-poly-eval))))

(defthm rpb-iterate-width
  (implies (and (rationalp (rpb-lo interval))
                (rationalp (rpb-hi interval)))
           (equal (rpb-width (rpb-iterate precision poly interval))
                  (* (rusqrt-dyadic-width precision)
                     (rpb-width interval))))
  :hints (("Goal"
           :use ((:instance rpb-iterate-width-invariant))
           :in-theory (enable rpb-rational-intervalp))))

(defthm rpb-build-preserves-sign-bracket
  (implies (rpb-sign-bracketp poly (cons lo hi))
           (rpb-sign-bracketp poly (rpb-build precision poly lo hi)))
  :hints (("Goal"
           :use ((:instance rpb-sign-bracketp-of-iterate
                            (interval (cons lo hi))))
           :in-theory
           (union-theories '(rpb-build)
                           (theory 'minimal-theory)))))

(defthm rpb-build-width
  (implies (and (rationalp lo) (rationalp hi))
           (equal (rpb-width (rpb-build precision poly lo hi))
                  (* (rusqrt-dyadic-width precision)
                     (- hi lo))))
  :hints (("Goal"
           :use ((:instance rpb-iterate-width
                            (interval (cons lo hi))))
           :in-theory (enable rpb-build rpb-width rpb-lo rpb-hi))))

; A total, deliberately conservative selector.  If the initial bracket has
; width at most one, denominator(epsilon) bisections suffice.
(defthm rpb-dyadic-width-upper-bound
  (implies (natp n)
           (<= (rusqrt-dyadic-width n) (/ (+ 1 n))))
  :hints (("Goal"
           :induct (rusqrt-dyadic-width n)
           :in-theory (enable rusqrt-dyadic-width)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rpb-reciprocal-one-plus-denominator-below-positive-rational
  (implies (and (rationalp eps) (< 0 eps))
           (<= (/ (+ 1 (denominator eps))) eps))
  :hints (("Goal"
           :use ((:instance rational-implies2 (x eps))
                 (:instance numerator-positive (x eps)))
           :nonlinearp t))
  :rule-classes :linear)

(defun rpb-precision-for-epsilon (eps)
  (if (and (rationalp eps) (< 0 eps))
      (denominator eps)
    0))

(defthm natp-of-rpb-precision-for-epsilon
  (natp (rpb-precision-for-epsilon eps))
  :hints (("Goal" :in-theory (enable rpb-precision-for-epsilon))))

(defthm rpb-precision-for-epsilon-suffices
  (implies (and (rationalp eps) (< 0 eps))
           (<= (rusqrt-dyadic-width
                (rpb-precision-for-epsilon eps))
               eps))
  :hints (("Goal"
           :use ((:instance rpb-dyadic-width-upper-bound
                            (n (denominator eps)))
                 (:instance
                  rpb-reciprocal-one-plus-denominator-below-positive-rational))
           :in-theory (enable rpb-precision-for-epsilon))))

(defthm rpb-generated-bracket-has-requested-width
  (implies (and (rationalp eps)
                (< 0 eps)
                (rationalp lo)
                (rationalp hi)
                (<= 0 (- hi lo))
                (<= (- hi lo) 1))
           (<= (rpb-width
                (rpb-build (rpb-precision-for-epsilon eps)
                           poly lo hi))
               eps))
  :hints (("Goal"
           :use ((:instance rpb-build-width
                            (precision (rpb-precision-for-epsilon eps)))
                 (:instance rpb-precision-for-epsilon-suffices))
           :nonlinearp t)))
