; Coefficient functionals and monomial probes for universal Toom-Cook moments.
(in-package "ACL2")
(include-book "zbp-rational-lagrange-reconstruction")
(include-book "arithmetic-5/top" :dir :system)

(defun tc-nth-scale-induct (k xs)
  (declare (xargs :measure (nfix k)))
  (if (or (zp k) (endp xs))
      (list k xs)
    (tc-nth-scale-induct (1- k) (cdr xs))))

(defthm tc-nth0-of-nil-total
  (equal (tc-nth0 k nil) 0)
  :hints (("Goal" :induct (tc-nth0 k nil)
                   :in-theory (enable tc-nth0))))

(defthm tc-poly-scale-when-endp
  (implies (endp p)
           (equal (tc-poly-scale c p) nil))
  :hints (("Goal" :expand ((tc-poly-scale c p))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-poly-scale-open
  (implies (consp p)
           (equal (tc-poly-scale c p)
                  (cons (* c (car p))
                        (tc-poly-scale c (cdr p)))))
  :hints (("Goal" :expand ((tc-poly-scale c p))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-nth0-when-zp
  (implies (zp k)
           (equal (tc-nth0 k xs)
                  (if (consp xs) (car xs) 0)))
  :hints (("Goal" :expand ((tc-nth0 k xs))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-nth0-open-positive
  (implies (not (zp k))
           (equal (tc-nth0 k xs)
                  (tc-nth0 (1- k) (cdr xs))))
  :hints (("Goal" :expand ((tc-nth0 k xs))
                   :in-theory (theory 'minimal-theory))))


(defthm tc-nth0-when-not-consp
  (implies (not (consp xs))
           (equal (tc-nth0 k xs) 0))
  :hints (("Goal" :induct (tc-nth0 k xs)
                   :in-theory (enable tc-nth0))))

(defthm tc-nth0-of-tc-poly-scale-total
  (implies (rationalp c)
           (equal (tc-nth0 k (tc-poly-scale c p))
                  (* c (tc-nth0 k p))))
  :hints
  (("Goal"
    :induct (tc-nth-scale-induct k p)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-nth-scale-induct)
       (:definition tc-nth-scale-induct)
       tc-poly-scale-when-endp
       tc-poly-scale-open
       tc-nth0-when-zp
       tc-nth0-open-positive
       tc-nth0-of-nil-total
       tc-nth0-when-not-consp
       car-cons cdr-cons
       rationalp-implies-acl2-numberp)))))

(defun tc-nth-add-induct (k a b)
  (declare (xargs :measure (nfix k)))
  (if (or (zp k) (and (endp a) (endp b)))
      (list k a b)
    (tc-nth-add-induct (1- k) (cdr a) (cdr b))))

(defthm tc-poly-add-when-left-endp
  (implies (endp a)
           (equal (tc-poly-add a b) b))
  :hints (("Goal" :expand ((tc-poly-add a b))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-poly-add-when-right-endp
  (implies (and (endp b) (consp a))
           (equal (tc-poly-add a b) a))
  :hints (("Goal" :expand ((tc-poly-add a b))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-poly-add-open
  (implies (and (consp a) (consp b))
           (equal (tc-poly-add a b)
                  (cons (+ (car a) (car b))
                        (tc-poly-add (cdr a) (cdr b)))))
  :hints (("Goal" :expand ((tc-poly-add a b))
                   :in-theory (theory 'minimal-theory))))

(defthm tc-rationalp-of-tc-nth0-basic
  (implies (rational-listp xs)
           (rationalp (tc-nth0 k xs)))
  :hints
  (("Goal"
    :induct (tc-nth-scale-induct k xs)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-nth-scale-induct)
       (:definition tc-nth-scale-induct)
       rational-listp
       tc-nth0-when-zp
       tc-nth0-open-positive
       tc-nth0-when-not-consp
       rationalp)))))

(defthm tc-nth0-of-tc-poly-add-total
  (implies (and (rational-listp a)
                (rational-listp b))
           (equal (tc-nth0 k (tc-poly-add a b))
                  (+ (tc-nth0 k a) (tc-nth0 k b))))
  :hints
  (("Goal"
    :induct (tc-nth-add-induct k a b)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-nth-add-induct)
       (:definition tc-nth-add-induct)
       tc-poly-add-when-left-endp
       tc-poly-add-when-right-endp
       tc-poly-add-open
       tc-nth0-when-zp
       tc-nth0-open-positive
       tc-nth0-of-nil-total
       tc-nth0-when-not-consp
       rational-listp
       tc-rationalp-of-tc-nth0-basic
       rationalp-implies-acl2-numberp
       car-cons cdr-cons)))))

(defun tc-lagrange-coeff-sum-aux (count point m p k)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (* (tc-poly-eval p (nfix point))
          (tc-nth0 k (tc-lagrange-row m (nfix point))))
       (tc-lagrange-coeff-sum-aux
        (1- count) (1+ (nfix point)) m p k))))

(defthm tc-lagrange-coeff-sum-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-coeff-sum-aux count point m p k) 0))
  :hints (("Goal"
           :expand ((tc-lagrange-coeff-sum-aux count point m p k))
           :in-theory (theory 'minimal-theory))))

(defthm tc-lagrange-coeff-sum-aux-open
  (implies (not (zp count))
           (equal
            (tc-lagrange-coeff-sum-aux count point m p k)
            (+ (* (tc-poly-eval p (nfix point))
                  (tc-nth0 k (tc-lagrange-row m (nfix point))))
               (tc-lagrange-coeff-sum-aux
                (1- count) (1+ (nfix point)) m p k))))
  :hints (("Goal"
           :expand ((tc-lagrange-coeff-sum-aux count point m p k))
           :in-theory (theory 'minimal-theory))))

(defthm tc-nth0-of-lagrange-reconstruct-step
  (implies (and (natp count)
                (not (zp count))
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (rational-listp p)
                (natp k))
           (equal
            (tc-nth0
             k
             (tc-poly-add
              (tc-poly-scale
               (tc-poly-eval p point)
               (tc-lagrange-row m point))
              (tc-lagrange-reconstruct-aux
               (1- count) (1+ point) m p)))
            (+ (* (tc-poly-eval p point)
                  (tc-nth0 k (tc-lagrange-row m point)))
               (tc-nth0
                k
                (tc-lagrange-reconstruct-aux
                 (1- count) (1+ point) m p)))))
  :hints
  (("Goal"
    :use
    ((:instance rationalp-of-tc-poly-eval (x point))
     (:instance rational-listp-of-tc-lagrange-row
                (point point))
     (:instance rational-listp-of-tc-poly-scale
                (c (tc-poly-eval p point))
                (p (tc-lagrange-row m point)))
     (:instance rational-listp-of-tc-lagrange-reconstruct-aux
                (count (1- count))
                (point (1+ point)))
     (:instance tc-nth0-of-tc-poly-add-total
                (a (tc-poly-scale
                    (tc-poly-eval p point)
                    (tc-lagrange-row m point)))
                (b (tc-lagrange-reconstruct-aux
                    (1- count) (1+ point) m p)))
     (:instance tc-nth0-of-tc-poly-scale-total
                (c (tc-poly-eval p point))
                (p (tc-lagrange-row m point))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(tc-current-point-below-bound
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-rationalp-when-natp
       rationalp-implies-acl2-numberp)))))

(defthm tc-nth0-of-lagrange-reconstruct-aux
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (rational-listp p)
                (natp k))
           (equal
            (tc-nth0 k
                     (tc-lagrange-reconstruct-aux count point m p))
            (tc-lagrange-coeff-sum-aux count point m p k)))
  :hints
  (("Goal"
    :induct (tc-lagrange-reconstruct-aux count point m p)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-lagrange-reconstruct-aux)
       tc-lagrange-reconstruct-aux-when-zp
       tc-lagrange-reconstruct-aux-open
       tc-lagrange-coeff-sum-aux-when-zp
       tc-lagrange-coeff-sum-aux-open
       tc-nth0-of-lagrange-reconstruct-step
       tc-nth0-of-nil-total
       tc-nth0-of-tc-poly-scale-total
       tc-nth0-of-tc-poly-add-total
       tc-nfix-when-natp
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-current-point-below-bound
       tc-successor-interval-bound
       rationalp-of-tc-poly-eval
       rational-listp-of-tc-lagrange-row
       rational-listp-of-tc-poly-scale
       rational-listp-of-tc-lagrange-reconstruct-aux)))))

(defun tc-zero-coeffs (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (tc-zero-coeffs (1- count)))))

(defun tc-monomial-coeffs (count degree)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (zp degree)
        (cons 1 (tc-zero-coeffs (1- count)))
      (cons 0 (tc-monomial-coeffs (1- count) (1- degree))))))

(defthm len-of-tc-zero-coeffs
  (equal (len (tc-zero-coeffs count)) (nfix count))
  :hints (("Goal" :induct (tc-zero-coeffs count)
                   :in-theory (enable tc-zero-coeffs))))

(defthm rational-listp-of-tc-zero-coeffs
  (rational-listp (tc-zero-coeffs count))
  :hints (("Goal" :induct (tc-zero-coeffs count)
                   :in-theory (enable tc-zero-coeffs))))

(defthm tc-zero-coeffs-when-zp
  (implies (zp count)
           (equal (tc-zero-coeffs count) nil))
  :hints (("Goal"
           :expand ((tc-zero-coeffs count))
           :in-theory (theory 'minimal-theory))))

(defthm tc-zero-coeffs-open
  (implies (not (zp count))
           (equal (tc-zero-coeffs count)
                  (cons 0 (tc-zero-coeffs (1- count)))))
  :hints (("Goal"
           :expand ((tc-zero-coeffs count))
           :in-theory (theory 'minimal-theory))))

(defthm tc-poly-eval-of-cons-basic
  (equal (tc-poly-eval (cons a p) x)
         (+ a (* x (tc-poly-eval p x))))
  :hints (("Goal"
           :expand ((tc-poly-eval (cons a p) x))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))

(defthm tc-poly-eval-of-tc-zero-coeffs
  (equal (tc-poly-eval (tc-zero-coeffs count) x) 0)
  :hints
  (("Goal"
    :induct (tc-zero-coeffs count)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-zero-coeffs)
       tc-zero-coeffs-when-zp
       tc-zero-coeffs-open
       tc-poly-eval-of-nil
       tc-poly-eval-of-cons-basic)))))

(defthm len-of-tc-monomial-coeffs
  (equal (len (tc-monomial-coeffs count degree)) (nfix count))
  :hints (("Goal" :induct (tc-monomial-coeffs count degree)
                   :in-theory (enable tc-monomial-coeffs))))

(defthm rational-listp-of-tc-monomial-coeffs
  (rational-listp (tc-monomial-coeffs count degree))
  :hints (("Goal" :induct (tc-monomial-coeffs count degree)
                   :in-theory (enable tc-monomial-coeffs))))

(defthm tc-monomial-coeffs-when-count-zp
  (implies (zp count)
           (equal (tc-monomial-coeffs count degree) nil))
  :hints (("Goal"
           :expand ((tc-monomial-coeffs count degree))
           :in-theory (theory 'minimal-theory))))

(defthm tc-monomial-coeffs-when-degree-zp
  (implies (and (not (zp count)) (zp degree))
           (equal (tc-monomial-coeffs count degree)
                  (cons 1 (tc-zero-coeffs (1- count)))))
  :hints (("Goal"
           :expand ((tc-monomial-coeffs count degree))
           :in-theory (theory 'minimal-theory))))

(defthm tc-monomial-coeffs-open-positive
  (implies (and (not (zp count)) (not (zp degree)))
           (equal (tc-monomial-coeffs count degree)
                  (cons 0
                        (tc-monomial-coeffs
                         (1- count) (1- degree)))))
  :hints (("Goal"
           :expand ((tc-monomial-coeffs count degree))
           :in-theory (theory 'minimal-theory))))

(defthm tc-predecessors-preserve-strict-order
  (implies (and (natp a) (natp b)
                (not (zp a)) (< a b))
           (< (1- a) (1- b))))

(defthm tc-expt-open-positive-natural
  (implies (and (natp degree) (not (zp degree)))
           (equal (expt x degree)
                  (* x (expt x (1- degree)))))
  :hints (("Goal" :expand ((expt x degree)))))

(defthm tc-natural-less-than-zp-impossible
  (implies (and (natp count) (zp count)
                (natp degree))
           (not (< degree count)))
  :hints (("Goal"
           :use ((:instance tc-zp-natural-is-zero (m count))))))

(defthm tc-one-plus-times-zero
  (implies (rationalp x)
           (equal (+ 1 (* x 0)) 1)))

(defthm tc-expt-of-zp-natural
  (implies (and (natp degree) (zp degree))
           (equal (expt x degree) 1))
  :hints (("Goal"
           :use ((:instance tc-zp-natural-is-zero (m degree))))))

(defthm tc-poly-eval-of-tc-monomial-coeffs
  (implies (and (natp count)
                (natp degree)
                (< degree count)
                (rationalp x))
           (equal (tc-poly-eval (tc-monomial-coeffs count degree) x)
                  (expt x degree)))
  :hints
  (("Goal"
    :induct (tc-monomial-coeffs count degree)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-monomial-coeffs)
       tc-monomial-coeffs-when-count-zp
       tc-monomial-coeffs-when-degree-zp
       tc-monomial-coeffs-open-positive
       tc-poly-eval-of-nil
       tc-poly-eval-of-cons-basic
       tc-poly-eval-of-tc-zero-coeffs
       tc-natp-of-one-less-when-positive
       tc-predecessors-preserve-strict-order
       tc-expt-open-positive-natural
       tc-natural-less-than-zp-impossible
       tc-one-plus-times-zero
       tc-expt-of-zp-natural
       rationalp-implies-acl2-numberp)))))

(defun tc-zero-listp (xs)
  (if (endp xs)
      t
    (and (equal (car xs) 0)
         (tc-zero-listp (cdr xs)))))

(defthm tc-zero-listp-of-tc-zero-coeffs
  (tc-zero-listp (tc-zero-coeffs count))
  :hints
  (("Goal"
    :induct (tc-zero-coeffs count)
    :in-theory (enable tc-zero-listp tc-zero-coeffs))))

(defthm tc-zero-listp-when-endp
  (implies (endp xs)
           (tc-zero-listp xs))
  :hints (("Goal"
           :expand ((tc-zero-listp xs))
           :in-theory (theory 'minimal-theory))))

(defthm tc-zero-listp-open
  (implies (consp xs)
           (equal (tc-zero-listp xs)
                  (and (equal (car xs) 0)
                       (tc-zero-listp (cdr xs)))))
  :hints (("Goal"
           :expand ((tc-zero-listp xs))
           :in-theory (theory 'minimal-theory))))

(defthm tc-zero-listp-of-cdr
  (implies (tc-zero-listp xs)
           (tc-zero-listp (cdr xs)))
  :hints (("Goal"
           :cases ((consp xs))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-zero-listp-open
              tc-zero-listp-when-endp
              cdr-cons)))))

(defthm tc-nth0-of-tc-zero-listp
  (implies (tc-zero-listp xs)
           (equal (tc-nth0 k xs) 0))
  :hints
  (("Goal"
    :induct (tc-nth0 k xs)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-nth0)
       tc-zero-listp-when-endp
       tc-zero-listp-open
       tc-zero-listp-of-cdr
       tc-nth0-when-zp
       tc-nth0-open-positive
       tc-nth0-when-not-consp)))))

(defthm tc-nth0-of-tc-zero-coeffs
  (equal (tc-nth0 k (tc-zero-coeffs count)) 0)
  :hints
  (("Goal"
    :use ((:instance tc-zero-listp-of-tc-zero-coeffs)
           (:instance tc-nth0-of-tc-zero-listp
                      (xs (tc-zero-coeffs count))))
    :in-theory (theory 'minimal-theory))))

(defun tc-monomial-nth-induct (count degree k)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (zp degree) (zp k))
      (list count degree k)
    (tc-monomial-nth-induct
     (1- count) (1- degree) (1- k))))

(defthm tc-zp-naturals-equal
  (implies (and (natp a) (natp b) (zp a) (zp b))
           (equal (equal a b) t))
  :hints (("Goal"
           :use ((:instance tc-zp-natural-is-zero (m a))
                 (:instance tc-zp-natural-is-zero (m b))))))

(defthm tc-zp-natural-distinct-from-positive
  (implies (and (natp a) (natp b) (zp a) (not (zp b)))
           (not (equal a b))))

(defthm tc-positive-natural-equality-by-predecessors
  (implies (and (natp a) (natp b)
                (not (zp a)) (not (zp b)))
           (equal (equal (1- a) (1- b))
                  (equal a b))))

(defthm tc-degree-zp-distinct-implies-k-positive
  (implies (and (natp degree) (natp k)
                (zp degree) (not (equal k degree)))
           (not (zp k)))
  :hints (("Goal"
           :use ((:instance tc-zp-naturals-equal
                            (a k) (b degree))))))

(defthm tc-k-zp-distinct-implies-degree-positive
  (implies (and (natp degree) (natp k)
                (zp k) (not (equal k degree)))
           (not (zp degree)))
  :hints (("Goal"
           :use ((:instance tc-zp-naturals-equal
                            (a k) (b degree))))))

(defthm tc-not-zp-count-when-natural-below
  (implies (and (natp value) (natp count) (< value count))
           (not (zp count))))

(defthm tc-nth0-of-tc-monomial-coeffs
  (implies (and (natp count)
                (natp degree)
                (< degree count)
                (natp k)
                (< k count))
           (equal (tc-nth0 k (tc-monomial-coeffs count degree))
                  (if (equal k degree) 1 0)))
  :hints
  (("Goal"
    :induct (tc-monomial-nth-induct count degree k)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-monomial-nth-induct)
       (:definition tc-monomial-nth-induct)
       tc-monomial-coeffs-when-count-zp
       tc-monomial-coeffs-when-degree-zp
       tc-monomial-coeffs-open-positive
       tc-nth0-when-zp
       tc-nth0-open-positive
       tc-nth0-of-tc-zero-coeffs
       tc-natural-less-than-zp-impossible
       tc-not-zp-count-when-natural-below
       tc-natp-of-one-less-when-positive
       tc-predecessors-preserve-strict-order
       tc-zp-naturals-equal
       tc-zp-natural-distinct-from-positive
       tc-degree-zp-distinct-implies-k-positive
       tc-k-zp-distinct-implies-degree-positive
       tc-positive-natural-equality-by-predecessors
       car-cons cdr-cons)))))
