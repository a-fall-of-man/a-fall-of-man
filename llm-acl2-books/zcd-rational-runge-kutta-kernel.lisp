; A small, purely rational Runge--Kutta certificate kernel.
(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(include-book "std/lists/top" :dir :system)

(defun qrk-sum (xs)
  (if (endp xs)
      0
    (+ (car xs) (qrk-sum (cdr xs)))))

(defun qrk-dot (weights slopes)
  (if (or (endp weights) (endp slopes))
      0
    (+ (* (car weights) (car slopes))
       (qrk-dot (cdr weights) (cdr slopes)))))

(defun qrk-nonnegative-listp (xs)
  (if (consp xs)
      (and (rationalp (car xs))
           (<= 0 (car xs))
           (qrk-nonnegative-listp (cdr xs)))
    (equal xs nil)))

(defun qrk-between-listp (lo hi xs)
  (if (consp xs)
      (and (rationalp (car xs))
           (<= lo (car xs))
           (<= (car xs) hi)
           (qrk-between-listp lo hi (cdr xs)))
    (equal xs nil)))

(defun qrk-consistent-weights-p (weights)
  (and (qrk-nonnegative-listp weights)
       (equal (qrk-sum weights) 1)))

(defun qrk-step-from-slopes (y h weights slopes)
  (+ y (* h (qrk-dot weights slopes))))

(defthm rationalp-of-qrk-sum
  (implies (rational-listp xs)
           (rationalp (qrk-sum xs))))

(defthm rationalp-of-qrk-dot
  (implies (and (rational-listp weights)
                (rational-listp slopes))
           (rationalp (qrk-dot weights slopes))))

(defthm rationalp-of-qrk-step-from-slopes
  (implies (and (rationalp y)
                (rationalp h)
                (rational-listp weights)
                (rational-listp slopes))
           (rationalp (qrk-step-from-slopes y h weights slopes))))

(defthm qrk-nonnegative-listp-implies-rational-listp
  (implies (qrk-nonnegative-listp xs)
           (rational-listp xs)))

(defthm qrk-between-listp-implies-rational-listp
  (implies (qrk-between-listp lo hi xs)
           (rational-listp xs)))

(defthm qrk-nonnegative-factor-preserves-lower-bound
  (implies (and (rationalp weight)
                (rationalp lo)
                (rationalp x)
                (<= 0 weight)
                (<= lo x))
           (<= (* weight lo) (* weight x)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm qrk-nonnegative-factor-preserves-upper-bound
  (implies (and (rationalp weight)
                (rationalp hi)
                (rationalp x)
                (<= 0 weight)
                (<= x hi))
           (<= (* weight x) (* weight hi)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm qrk-dot-lower-bound
  (implies (and (rationalp lo)
                (rationalp hi)
                (qrk-nonnegative-listp weights)
                (qrk-between-listp lo hi slopes)
                (equal (len weights) (len slopes)))
           (<= (* lo (qrk-sum weights))
               (qrk-dot weights slopes)))
  :hints (("Goal"
           :induct (qrk-dot weights slopes)
           :in-theory (enable qrk-dot qrk-sum
                              qrk-nonnegative-listp
                              qrk-between-listp))
          ("Subgoal *1/2"
           :use ((:instance qrk-nonnegative-factor-preserves-lower-bound
                            (weight (car weights))
                            (x (car slopes))))
           :in-theory (enable qrk-dot qrk-sum
                              qrk-nonnegative-listp
                              qrk-between-listp)))
  :rule-classes :linear)

(defthm qrk-dot-upper-bound
  (implies (and (rationalp hi)
                (rationalp lo)
                (qrk-nonnegative-listp weights)
                (qrk-between-listp lo hi slopes)
                (equal (len weights) (len slopes)))
           (<= (qrk-dot weights slopes)
               (* hi (qrk-sum weights))))
  :hints (("Goal"
           :induct (qrk-dot weights slopes)
           :in-theory (enable qrk-dot qrk-sum
                              qrk-nonnegative-listp
                              qrk-between-listp))
          ("Subgoal *1/2"
           :use ((:instance qrk-nonnegative-factor-preserves-upper-bound
                            (weight (car weights))
                            (x (car slopes))))
           :in-theory (enable qrk-dot qrk-sum
                              qrk-nonnegative-listp
                              qrk-between-listp)))
  :rule-classes :linear)

(defthm qrk-step-from-slopes-enclosed
  (implies (and (rationalp y)
                (rationalp h)
                (rationalp lo)
                (rationalp hi)
                (<= 0 h)
                (qrk-consistent-weights-p weights)
                (qrk-between-listp lo hi slopes)
                (equal (len weights) (len slopes)))
           (and (<= (+ y (* h lo))
                    (qrk-step-from-slopes y h weights slopes))
                (<= (qrk-step-from-slopes y h weights slopes)
                    (+ y (* h hi)))))
  :hints (("Goal"
           :use ((:instance qrk-dot-lower-bound)
                 (:instance qrk-dot-upper-bound))
           :in-theory (enable qrk-step-from-slopes
                              qrk-consistent-weights-p)
           :nonlinearp t)))

