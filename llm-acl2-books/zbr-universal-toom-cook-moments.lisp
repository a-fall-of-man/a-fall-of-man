; Universal moment semantics for the generated rational Toom-Cook bank.
(in-package "ACL2")
(include-book "zbq-universal-toom-cook-certificate")
(include-book "arithmetic-5/top" :dir :system)

(defthm tc-lagrange-bank-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-bank-aux count point m) nil))
  :hints (("Goal"
           :expand ((tc-lagrange-bank-aux count point m))
           :in-theory (theory 'minimal-theory))))

(defthm tc-lagrange-bank-aux-open
  (implies (not (zp count))
           (equal (tc-lagrange-bank-aux count point m)
                  (cons (tc-lagrange-row m (nfix point))
                        (tc-lagrange-bank-aux
                         (1- count) (1+ (nfix point)) m))))
  :hints (("Goal"
           :expand ((tc-lagrange-bank-aux count point m))
           :in-theory (theory 'minimal-theory))))

(defthm tc-post-row-from-bank-of-nil
  (equal (tc-post-row-from-bank n out nil) nil)
  :hints (("Goal"
           :expand ((tc-post-row-from-bank n out nil))
           :in-theory (theory 'minimal-theory))))

(defthm tc-post-row-from-bank-of-cons
  (equal (tc-post-row-from-bank n out (cons row bank))
         (cons (+ (tc-nth0 out row)
                  (tc-nth0 (+ (nfix out) (nfix n)) row))
               (tc-post-row-from-bank n out bank)))
  :hints (("Goal"
           :expand ((tc-post-row-from-bank n out (cons row bank)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))

(defthm tc-row-moment-aux-of-nil
  (equal (tc-row-moment-aux nil point degree acc) acc)
  :hints (("Goal"
           :expand ((tc-row-moment-aux nil point degree acc))
           :in-theory (theory 'minimal-theory))))

(defthm tc-row-moment-aux-of-cons
  (equal (tc-row-moment-aux (cons coefficient post)
                            point degree acc)
         (tc-row-moment-aux
          post (1+ (nfix point)) degree
          (+ acc (* coefficient
                    (expt (nfix point) (nfix degree))))))
  :hints (("Goal"
           :expand ((tc-row-moment-aux (cons coefficient post)
                                       point degree acc))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))



(defthm tc-nth0-open-when-consp
  (implies (consp row)
           (equal (tc-nth0 k row)
                  (if (zp k)
                      (car row)
                    (tc-nth0 (1- k) (cdr row)))))
  :hints (("Goal"
           :expand ((tc-nth0 k row))
           :in-theory (theory 'minimal-theory))))

(defthm tc-rationalp-of-tc-nth0
  (implies (rational-listp row)
           (rationalp (tc-nth0 k row)))
  :hints
  (("Goal"
    :induct (tc-nth-scale-induct k row)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-nth-scale-induct)
       tc-nth0-open-when-consp
       tc-nth0-of-nil-total
       rational-listp)))))

(defthm tc-rationalp-of-natural-expt
  (implies (and (natp base) (natp degree))
           (rationalp (expt base degree))))

(defthm tc-rationalp-of-sum
  (implies (and (rationalp a) (rationalp b))
           (rationalp (+ a b))))

(defthm tc-rationalp-of-product
  (implies (and (rationalp a) (rationalp b))
           (rationalp (* a b))))

(defthm tc-rationalp-of-lagrange-coeff-sum-aux
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (rational-listp p))
           (rationalp
            (tc-lagrange-coeff-sum-aux count point m p k)))
  :hints
  (("Goal"
    :induct (tc-lagrange-coeff-sum-aux count point m p k)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-lagrange-coeff-sum-aux)
       tc-lagrange-coeff-sum-aux-when-zp
       tc-lagrange-coeff-sum-aux-open
       tc-current-point-below-bound
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-nfix-when-natp
       tc-rationalp-when-natp
       rationalp-of-tc-poly-eval
       rational-listp-of-tc-lagrange-row
       tc-rationalp-of-tc-nth0
       tc-rationalp-of-product
       tc-rationalp-of-sum)))))

(defthm tc-rationalp-of-generated-moment-accumulator-step
  (implies
   (and (natp count)
        (not (zp count))
        (natp point)
        (natp m)
        (<= (+ point count) m)
        (natp n)
        (natp out)
        (natp degree)
        (rationalp acc))
   (rationalp
    (+ acc
       (* (+ (tc-nth0 out (tc-lagrange-row m point))
             (tc-nth0 (+ out n) (tc-lagrange-row m point)))
          (expt point degree)))))
  :hints
  (("Goal"
    :use ((:instance tc-current-point-below-bound)
          (:instance rational-listp-of-tc-lagrange-row)
          (:instance tc-rationalp-of-tc-nth0
                     (row (tc-lagrange-row m point)) (k out))
          (:instance tc-rationalp-of-tc-nth0
                     (row (tc-lagrange-row m point)) (k (+ out n)))
          (:instance tc-rationalp-of-natural-expt
                     (base point)))
    :in-theory (theory 'minimal-theory))))

(defun tc-generated-row-moment-induct
  (count point m n out degree acc)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list point m n out degree acc)
    (tc-generated-row-moment-induct
     (1- count) (1+ (nfix point)) m n out degree
     (+ acc
        (* (+ (tc-nth0 out
                        (tc-lagrange-row m (nfix point)))
              (tc-nth0 (+ (nfix out) (nfix n))
                        (tc-lagrange-row m (nfix point))))
           (expt (nfix point) (nfix degree)))))))

(defthm tc-two-channel-accumulator-algebra
  (implies (and (rationalp acc)
                (rationalp a)
                (rationalp b)
                (rationalp e)
                (rationalp left-tail)
                (rationalp right-tail))
           (equal (+ (+ acc (* (+ a b) e))
                     left-tail right-tail)
                  (+ acc
                     (+ (* e a) left-tail)
                     (* e b) right-tail))))

(defthm tc-generated-row-moment-as-two-coefficient-sums
  (implies
   (and (natp count)
        (natp point)
        (natp m)
        (<= (+ point count) m)
        (natp degree)
        (< degree m)
        (natp n)
        (natp out)
        (rationalp acc))
   (equal
    (tc-row-moment-aux
     (tc-post-row-from-bank
      n out (tc-lagrange-bank-aux count point m))
     point degree acc)
    (+ acc
       (tc-lagrange-coeff-sum-aux
        count point m (tc-monomial-coeffs m degree) out)
       (tc-lagrange-coeff-sum-aux
        count point m (tc-monomial-coeffs m degree)
        (+ out n)))))
  :hints
  (("Goal"
    :induct (tc-generated-row-moment-induct
             count point m n out degree acc)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-generated-row-moment-induct)
       tc-lagrange-bank-aux-when-zp
       tc-lagrange-bank-aux-open
       tc-post-row-from-bank-of-nil
       tc-post-row-from-bank-of-cons
       tc-row-moment-aux-of-nil
       tc-row-moment-aux-of-cons
       tc-lagrange-coeff-sum-aux-when-zp
       tc-lagrange-coeff-sum-aux-open
       tc-poly-eval-of-tc-monomial-coeffs
       tc-rationalp-of-tc-nth0
       rational-listp-of-tc-lagrange-row
       rational-listp-of-tc-monomial-coeffs
       tc-rationalp-of-natural-expt
       tc-current-point-below-bound
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-nfix-when-natp
       tc-rationalp-of-nfix
       tc-rationalp-when-natp
       tc-rationalp-of-lagrange-coeff-sum-aux
       tc-rationalp-of-generated-moment-accumulator-step
       tc-two-channel-accumulator-algebra)))))
