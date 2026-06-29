; Universal compact certificates for generated rational Toom-Cook plans.
(in-package "ACL2")
(include-book "zbr-universal-toom-cook-moments")
(include-book "arithmetic-5/top" :dir :system)

(defun tc-nth-beyond-induct (k xs)
  (declare (xargs :measure (nfix k)))
  (if (or (zp k) (endp xs))
      (list k xs)
    (tc-nth-beyond-induct (1- k) (cdr xs))))

(defthm tc-nth0-zero-when-at-or-beyond-length
  (implies (and (natp k)
                (<= (len xs) k))
           (equal (tc-nth0 k xs) 0))
  :hints
  (("Goal"
    :induct (tc-nth-beyond-induct k xs)
    :in-theory
    (e/d (tc-nth-beyond-induct tc-nth0)
         (tc-consp-second-from-equal-length
          tc-cdr-lengths-equal)))))

(defthm tc-nth0-of-tc-monomial-coeffs-total
  (implies (and (natp count)
                (natp degree)
                (< degree count)
                (natp k))
           (equal (tc-nth0 k (tc-monomial-coeffs count degree))
                  (if (equal k degree) 1 0)))
  :hints
  (("Goal"
    :cases ((< k count))
    :use
    ((:instance tc-nth0-of-tc-monomial-coeffs)
     (:instance tc-nth0-zero-when-at-or-beyond-length
                (xs (tc-monomial-coeffs count degree))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(len-of-tc-monomial-coeffs
       tc-nfix-when-natp)))))

(defthm tc-lagrange-coeff-sum-of-monomial-total
  (implies (and (natp m)
                (natp degree)
                (< degree m)
                (natp k))
           (equal
            (tc-lagrange-coeff-sum-aux
             m 0 m (tc-monomial-coeffs m degree) k)
            (if (equal k degree) 1 0)))
  :hints
  (("Goal"
    :use
    ((:instance
      tc-nth0-of-lagrange-reconstruct-aux
      (count m) (point 0)
      (p (tc-monomial-coeffs m degree)))
     (:instance
      tc-lagrange-reconstruction-coefficient-identity
      (p (tc-monomial-coeffs m degree)))
     (:instance
      tc-nth0-of-tc-monomial-coeffs-total
      (count m) (k k)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-lagrange-reconstruct)
       tc-natp-of-zero
       tc-nfix-when-natp
       rational-listp-of-tc-monomial-coeffs
       len-of-tc-monomial-coeffs)))))

(defthm tc-natp-of-generated-rank
  (implies (posp n)
           (natp (1- (* 2 n)))))

(defthm tc-natp-from-posp
  (implies (posp n) (natp n)))

(defthm tc-natp-of-output-plus-size
  (implies (and (natp out) (natp n))
           (natp (+ out n))))

(defthm tc-row-moment-of-generated-post-as-two-deltas
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (< degree (1- (* 2 n))))
   (equal
    (tc-row-moment (tc-post-row n out) degree)
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))))
  :hints
  (("Goal"
    :use
    ((:instance
      tc-generated-row-moment-as-two-coefficient-sums
      (count (1- (* 2 n)))
      (point 0)
      (m (1- (* 2 n)))
      (acc 0))
     (:instance
      tc-lagrange-coeff-sum-of-monomial-total
      (m (1- (* 2 n))) (k out))
     (:instance
      tc-lagrange-coeff-sum-of-monomial-total
      (m (1- (* 2 n))) (k (+ out n))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-row-moment)
       (:definition tc-post-row)
       (:definition tc-lagrange-bank)
       tc-natp-of-generated-rank
       tc-natp-from-posp
       tc-natp-of-output-plus-size
       tc-natp-of-zero)))))

(defthm tc-rationalp-of-natural-quotient
  (implies (and (natp x) (posp y))
           (rationalp (/ x y))))

(defthm tc-mod-natural-below
  (implies (and (natp x) (posp y) (< x y))
           (equal (mod x y) x))
  :hints
  (("Goal"
    :use ((:instance tc-rationalp-of-natural-quotient
                     (x x) (y y))
          (:instance mod-x-y-=-x (x x) (y y))))))

(defthm tc-mod-natural-between-one-and-two
  (implies (and (natp x)
                (posp y)
                (<= y x)
                (< x (* 2 y)))
           (equal (mod x y) (- x y)))
  :hints
  (("Goal"
    :use ((:instance tc-rationalp-of-natural-quotient
                     (x x) (y y)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(mod-x-y-=-x-y)))))

(defthm tc-two-deltas-below-modulus
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (< degree n))
   (equal
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))
    (if (equal degree out) 1 0)))
  :hints
  (("Goal"
    :cases ((equal out degree)
            (equal (+ out n) degree)))))

(defthm tc-two-deltas-above-modulus
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (<= n degree)
        (< degree (* 2 n)))
   (equal
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))
    (if (equal (- degree n) out) 1 0)))
  :hints
  (("Goal"
    :cases ((equal out degree)
            (equal (+ out n) degree)
            (equal (- degree n) out)))))

(defthm tc-two-deltas-below-modulus-as-modular-delta
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (< degree n))
   (equal
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))
    (if (equal (mod degree n) out) 1 0)))
  :hints
  (("Goal"
    :use ((:instance tc-two-deltas-below-modulus)
          (:instance tc-mod-natural-below (x degree) (y n)))
    :in-theory (theory 'minimal-theory))))

(defthm tc-two-deltas-above-modulus-as-modular-delta
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (<= n degree)
        (< degree (* 2 n)))
   (equal
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))
    (if (equal (mod degree n) out) 1 0)))
  :hints
  (("Goal"
    :use ((:instance tc-two-deltas-above-modulus)
          (:instance tc-mod-natural-between-one-and-two
                     (x degree) (y n)))
    :in-theory (theory 'minimal-theory))))

(defthm tc-two-deltas-equal-modular-delta
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (< degree (1- (* 2 n))))
   (equal
    (+ (if (equal out degree) 1 0)
       (if (equal (+ out n) degree) 1 0))
    (if (equal (mod degree n) out) 1 0)))
  :hints
  (("Goal"
    :cases ((< degree n))
    :use ((:instance tc-two-deltas-below-modulus-as-modular-delta)
          (:instance tc-two-deltas-above-modulus-as-modular-delta))
    :in-theory (theory 'minimal-theory))))

(defthm tc-row-moment-of-generated-post
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp degree)
        (< degree (1- (* 2 n))))
   (equal
    (tc-row-moment (tc-post-row n out) degree)
    (if (equal (mod degree n) out) 1 0)))
  :hints
  (("Goal"
    :use ((:instance tc-row-moment-of-generated-post-as-two-deltas)
          (:instance tc-two-deltas-equal-modular-delta))
    :in-theory (theory 'minimal-theory))))
