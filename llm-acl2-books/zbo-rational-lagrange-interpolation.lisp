; Universal rational Lagrange interpolation over consecutive natural nodes.
(in-package "ACL2")
(include-book "zbn-rational-polynomial-root-bound")
(include-book "arithmetic-5/top" :dir :system)

(defun tc-lagrange-product-aux (count point omitted x acc)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      acc
    (tc-lagrange-product-aux
     (1- count)
     (1+ (nfix point))
     omitted x
     (if (equal (nfix point) (nfix omitted))
         acc
       (* acc (- x (nfix point)))))))

(defthm tc-lagrange-product-at-omitted-is-denominator
  (equal (tc-lagrange-product-aux
          count point omitted (nfix omitted) acc)
         (tc-lagrange-denominator-aux
          count point omitted acc))
  :hints (("Goal"
           :induct (tc-lagrange-denominator-aux
                    count point omitted acc)
           :in-theory (enable tc-lagrange-product-aux
                              tc-lagrange-denominator-aux))))

(defthm rational-listp-of-tc-poly-add
  (implies (and (rational-listp a)
                (rational-listp b))
           (rational-listp (tc-poly-add a b)))
  :hints (("Goal" :induct (tc-poly-add a b)
           :in-theory (enable tc-poly-add))))

(defthm rational-listp-of-tc-poly-mul-linear
  (implies (and (rational-listp p)
                (rationalp root))
           (rational-listp (tc-poly-mul-linear p root)))
  :hints (("Goal"
           :in-theory (enable tc-poly-mul-linear))))

(defthm tc-rationalp-of-nfix
  (rationalp (nfix x)))

(defthm tc-lagrange-numerator-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-numerator-aux
                   count point omitted p)
                  p))
  :hints (("Goal"
           :expand ((tc-lagrange-numerator-aux
                     count point omitted p)))))

(defthm tc-lagrange-numerator-aux-open
  (implies (not (zp count))
           (equal (tc-lagrange-numerator-aux
                   count point omitted p)
                  (tc-lagrange-numerator-aux
                   (1- count)
                   (1+ (nfix point))
                   omitted
                   (if (equal (nfix point) (nfix omitted))
                       p
                     (tc-poly-mul-linear p (nfix point))))))
  :hints (("Goal"
           :expand ((tc-lagrange-numerator-aux
                     count point omitted p)))))

(defthm tc-lagrange-product-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-product-aux
                   count point omitted x acc)
                  acc))
  :hints (("Goal"
           :expand ((tc-lagrange-product-aux
                     count point omitted x acc)))))

(defthm tc-lagrange-product-aux-open
  (implies (not (zp count))
           (equal (tc-lagrange-product-aux
                   count point omitted x acc)
                  (tc-lagrange-product-aux
                   (1- count)
                   (1+ (nfix point))
                   omitted x
                   (if (equal (nfix point) (nfix omitted))
                       acc
                     (* acc (- x (nfix point)))))))
  :hints (("Goal"
           :expand ((tc-lagrange-product-aux
                     count point omitted x acc)))))

(defthm tc-poly-eval-of-lagrange-numerator-aux
  (implies (and (rational-listp p)
                (rationalp x))
           (equal (tc-poly-eval
                   (tc-lagrange-numerator-aux
                    count point omitted p)
                   x)
                  (tc-lagrange-product-aux
                   count point omitted x
                   (tc-poly-eval p x))))
  :hints (("Goal"
           :induct (tc-lagrange-numerator-aux
                    count point omitted p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-numerator-aux)
              tc-lagrange-numerator-aux-when-zp
              tc-lagrange-numerator-aux-open
              tc-lagrange-product-aux-when-zp
              tc-lagrange-product-aux-open
              tc-rationalp-of-nfix
              rational-listp-of-tc-poly-mul-linear
              tc-poly-eval-of-tc-poly-mul-linear
              commutativity-of-*)))))

(defthm rational-listp-of-tc-lagrange-numerator-aux
  (implies (rational-listp p)
           (rational-listp
            (tc-lagrange-numerator-aux count point omitted p)))
  :hints (("Goal"
           :induct (tc-lagrange-numerator-aux
                    count point omitted p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-numerator-aux)
              tc-lagrange-numerator-aux-when-zp
              tc-lagrange-numerator-aux-open
              tc-rationalp-of-nfix
              rational-listp-of-tc-poly-mul-linear)))))

(defthm rationalp-of-tc-lagrange-denominator-aux
  (implies (rationalp acc)
           (rationalp
            (tc-lagrange-denominator-aux
             count point omitted acc)))
  :hints (("Goal"
           :induct (tc-lagrange-denominator-aux
                    count point omitted acc)
           :in-theory (enable tc-lagrange-denominator-aux))))

(defthm tc-lagrange-denominator-aux-nonzero
  (implies (and (rationalp acc)
                (not (equal acc 0)))
           (not (equal
                 (tc-lagrange-denominator-aux
                  count point omitted acc)
                 0)))
  :hints (("Goal"
           :induct (tc-lagrange-denominator-aux
                    count point omitted acc)
           :in-theory (enable tc-lagrange-denominator-aux))))

(defthm tc-lagrange-product-aux-of-zero
  (equal (tc-lagrange-product-aux
          count point omitted x 0)
         0)
  :hints (("Goal"
           :induct (tc-lagrange-product-aux
                    count point omitted x 0)
           :in-theory (enable tc-lagrange-product-aux))))

(defthm tc-lagrange-product-zero-at-included-node
  (implies (and (natp count)
                (natp point)
                (natp omitted)
                (natp x)
                (<= point x)
                (< x (+ point count))
                (not (equal x omitted)))
           (equal (tc-lagrange-product-aux
                   count point omitted x acc)
                  0))
  :hints (("Goal"
           :induct (tc-lagrange-product-aux
                    count point omitted x acc)
           :in-theory (enable tc-lagrange-product-aux))))

(defthm tc-rational-listp-of-one
  (rational-listp '(1)))

(defthm tc-natp-of-zero
  (natp 0))

(defthm tc-natp-is-nonnegative
  (implies (natp x)
           (not (< x 0))))

(defthm tc-poly-eval-of-one
  (equal (tc-poly-eval '(1) x) 1)
  :hints (("Goal" :in-theory (enable tc-poly-eval))))

(defthm tc-reciprocal-times-nonzero-rational
  (implies (and (rationalp x)
                (not (equal x 0)))
           (equal (* (/ x) x) 1)))

(defthm tc-times-zero
  (equal (* x 0) 0))

(defthm tc-poly-eval-of-lagrange-numerator-at-own-node
  (implies (natp omitted)
           (equal (tc-poly-eval
                   (tc-lagrange-numerator-aux
                    m 0 omitted '(1))
                   omitted)
                  (tc-lagrange-denominator-aux
                   m 0 omitted 1)))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-lagrange-numerator-aux
                  (count m) (point 0) (p '(1)) (x omitted))
                 (:instance
                  tc-lagrange-product-at-omitted-is-denominator
                  (count m) (point 0) (acc 1)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-nfix-when-natp
              tc-rationalp-when-natp
              tc-poly-eval-of-one
              tc-rational-listp-of-one)))))

(defthm tc-poly-eval-of-lagrange-numerator-at-other-node
  (implies (and (natp m)
                (natp omitted)
                (< omitted m)
                (natp x)
                (< x m)
                (not (equal x omitted)))
           (equal (tc-poly-eval
                   (tc-lagrange-numerator-aux
                    m 0 omitted '(1))
                   x)
                  0))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-lagrange-numerator-aux
                  (count m) (point 0) (p '(1)))
                 (:instance
                  tc-lagrange-product-zero-at-included-node
                  (count m) (point 0) (acc 1)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-rationalp-when-natp
              tc-rational-listp-of-one
              tc-natp-of-zero
              tc-natp-is-nonnegative
              tc-poly-eval-of-one)))))

(defthm tc-poly-eval-of-lagrange-row-at-own-node
  (implies (and (natp m)
                (natp omitted)
                (< omitted m))
           (equal (tc-poly-eval
                   (tc-lagrange-row m omitted)
                   omitted)
                  1))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-tc-poly-scale
                  (c (/ (tc-lagrange-denominator-aux
                         m 0 omitted 1)))
                  (p (tc-lagrange-numerator-aux
                      m 0 omitted '(1)))
                  (x omitted))
                 (:instance
                  rational-listp-of-tc-lagrange-numerator-aux
                  (count m) (point 0) (p '(1)))
                 (:instance
                  rationalp-of-tc-lagrange-denominator-aux
                  (count m) (point 0) (acc 1))
                 (:instance
                  tc-lagrange-denominator-aux-nonzero
                  (count m) (point 0) (acc 1))
                 (:instance
                  tc-poly-eval-of-lagrange-numerator-at-own-node))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-lagrange-row)
              tc-rationalp-when-natp
              tc-rational-listp-of-one
              tc-reciprocal-times-nonzero-rational)))))

(defthm tc-poly-eval-of-lagrange-row-at-other-node
  (implies (and (natp m)
                (natp omitted)
                (< omitted m)
                (natp x)
                (< x m)
                (not (equal x omitted)))
           (equal (tc-poly-eval
                   (tc-lagrange-row m omitted)
                   x)
                  0))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-tc-poly-scale
                  (c (/ (tc-lagrange-denominator-aux
                         m 0 omitted 1)))
                  (p (tc-lagrange-numerator-aux
                      m 0 omitted '(1))))
                 (:instance
                  rational-listp-of-tc-lagrange-numerator-aux
                  (count m) (point 0) (p '(1)))
                 (:instance
                  rationalp-of-tc-lagrange-denominator-aux
                  (count m) (point 0) (acc 1))
                 (:instance
                  tc-poly-eval-of-lagrange-numerator-at-other-node))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-lagrange-row)
              tc-rationalp-when-natp
              tc-rational-listp-of-one
              tc-times-zero)))))

(defthm tc-poly-eval-of-lagrange-row
  (implies (and (natp m)
                (natp omitted)
                (< omitted m)
                (natp x)
                (< x m))
           (equal (tc-poly-eval
                   (tc-lagrange-row m omitted)
                   x)
                  (if (equal x omitted) 1 0)))
  :hints (("Goal"
           :cases ((equal x omitted))
           :use ((:instance tc-poly-eval-of-lagrange-row-at-own-node)
                 (:instance tc-poly-eval-of-lagrange-row-at-other-node))
           :in-theory (theory 'minimal-theory))))

(defthm len-of-tc-poly-add
  (equal (len (tc-poly-add a b))
         (max (len a) (len b)))
  :hints (("Goal" :induct (tc-poly-add a b)
           :in-theory (enable tc-poly-add))))

(defthm len-of-tc-poly-mul-linear
  (equal (len (tc-poly-mul-linear p root))
         (1+ (len p)))
  :hints (("Goal"
           :in-theory (enable tc-poly-mul-linear))))

(defun tc-lagrange-factor-count-aux (count point omitted)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (if (equal (nfix point) (nfix omitted)) 0 1)
       (tc-lagrange-factor-count-aux
        (1- count) (1+ (nfix point)) omitted))))

(defthm len-of-tc-lagrange-numerator-aux
  (equal (len (tc-lagrange-numerator-aux
               count point omitted p))
         (+ (len p)
            (tc-lagrange-factor-count-aux
             count point omitted)))
  :hints (("Goal"
           :induct (tc-lagrange-numerator-aux
                    count point omitted p)
           :in-theory (enable tc-lagrange-numerator-aux
                              tc-lagrange-factor-count-aux))))

(defthm tc-lagrange-factor-count-when-omitted-is-behind
  (implies (and (natp count)
                (natp point)
                (natp omitted)
                (< omitted point))
           (equal (tc-lagrange-factor-count-aux
                   count point omitted)
                  count))
  :hints (("Goal"
           :induct (tc-lagrange-factor-count-aux
                    count point omitted)
           :in-theory (enable tc-lagrange-factor-count-aux))))

(defthm tc-lagrange-factor-count-when-omitted-is-included
  (implies (and (natp count)
                (natp point)
                (natp omitted)
                (<= point omitted)
                (< omitted (+ point count)))
           (equal (tc-lagrange-factor-count-aux
                   count point omitted)
                  (1- count)))
  :hints (("Goal"
           :induct (tc-lagrange-factor-count-aux
                    count point omitted)
           :in-theory (enable tc-lagrange-factor-count-aux
                              tc-lagrange-factor-count-when-omitted-is-behind))))

(defthm len-of-tc-lagrange-row
  (implies (and (natp m)
                (natp point)
                (< point m))
           (equal (len (tc-lagrange-row m point)) m))
  :hints (("Goal"
           :use ((:instance len-of-tc-lagrange-numerator-aux
                            (count m) (point 0)
                            (omitted point) (p '(1)))
                 (:instance
                  tc-lagrange-factor-count-when-omitted-is-included
                  (count m) (point 0) (omitted point)))
           :in-theory (enable tc-lagrange-row))))

(defthm rational-listp-of-tc-lagrange-row
  (implies (and (natp m)
                (natp point)
                (< point m))
           (rational-listp (tc-lagrange-row m point)))
  :hints (("Goal"
           :use ((:instance
                  rational-listp-of-tc-lagrange-numerator-aux
                  (count m) (point 0) (omitted point) (p '(1)))
                 (:instance
                  rationalp-of-tc-lagrange-denominator-aux
                  (count m) (point 0) (omitted point) (acc 1)))
           :in-theory (enable tc-lagrange-row))))
