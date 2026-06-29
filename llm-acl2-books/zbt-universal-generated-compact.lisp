; Universal compact certification of the generated rational Toom-Cook bank.
(in-package "ACL2")
(include-book "zbs-universal-toom-cook-certificate")
(include-book "arithmetic-5/top" :dir :system)

(local
 (defthm zbt-nfix-when-zp
   (implies (zp count)
            (equal (nfix count) 0))
   :hints (("Goal" :in-theory (enable nfix zp)))))

(local
 (defthm zbt-nfix-step
   (implies (not (zp count))
            (equal (nfix count)
                   (1+ (nfix (1- count)))))
   :hints (("Goal" :in-theory (enable nfix zp)))))

(local
 (defthm zbt-bank-len-when-zp
   (implies (zp count)
            (equal (len (tc-lagrange-bank-aux count point m)) 0))
   :hints
   (("Goal"
     :use ((:instance tc-lagrange-bank-aux-when-zp))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(len))))))

(local
 (defthm zbt-bank-len-step
   (implies
    (not (zp count))
    (equal (len (tc-lagrange-bank-aux count point m))
           (1+ (len (tc-lagrange-bank-aux
                     (1- count) (1+ (nfix point)) m)))))
   :hints
   (("Goal"
     :use ((:instance tc-lagrange-bank-aux-open))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(len len-of-cons))))))

(defthm len-of-tc-lagrange-bank-aux
  (equal (len (tc-lagrange-bank-aux count point m))
         (nfix count))
  :hints
  (("Goal"
    :induct (tc-lagrange-bank-aux count point m)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-lagrange-bank-aux)
       zbt-nfix-when-zp
       zbt-nfix-step
       zbt-bank-len-when-zp
       zbt-bank-len-step)))))

(defthm tc-post-row-from-bank-when-endp
  (implies (endp bank)
           (equal (tc-post-row-from-bank n out bank) nil))
  :hints
  (("Goal"
    :expand ((tc-post-row-from-bank n out bank))
    :in-theory (theory 'minimal-theory))))

(defthm tc-post-row-from-bank-open-when-consp
  (implies (consp bank)
           (equal (tc-post-row-from-bank n out bank)
                  (cons (+ (tc-nth0 out (car bank))
                           (tc-nth0 (+ (nfix out) (nfix n))
                                    (car bank)))
                        (tc-post-row-from-bank n out (cdr bank)))))
  :hints
  (("Goal"
    :expand ((tc-post-row-from-bank n out bank))
    :in-theory (theory 'minimal-theory))))

(defthm len-of-tc-post-row-from-bank
  (equal (len (tc-post-row-from-bank n out bank))
         (len bank))
  :hints
  (("Goal"
    :induct (tc-post-row-from-bank n out bank)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-post-row-from-bank)
       tc-post-row-from-bank-when-endp
       tc-post-row-from-bank-open-when-consp
       len
       len-of-cons)))))

(defthm tc-rationalp-of-generated-post-head
  (implies
   (and (natp count)
        (not (zp count))
        (natp point)
        (natp m)
        (<= (+ point count) m)
        (natp n)
        (natp out))
   (rationalp
    (+ (tc-nth0 out (tc-lagrange-row m point))
       (tc-nth0 (+ out n) (tc-lagrange-row m point)))))
  :hints
  (("Goal"
    :use ((:instance tc-current-point-below-bound)
          (:instance rational-listp-of-tc-lagrange-row)
          (:instance tc-rationalp-of-tc-nth0
                     (row (tc-lagrange-row m point))
                     (k out))
          (:instance tc-rationalp-of-tc-nth0
                     (row (tc-lagrange-row m point))
                     (k (+ out n)))
          (:instance tc-rationalp-of-sum
                     (a (tc-nth0 out (tc-lagrange-row m point)))
                     (b (tc-nth0 (+ out n)
                                 (tc-lagrange-row m point)))))
    :in-theory (theory 'minimal-theory))))

(defthm tc-rational-listp-of-cons
  (equal (rational-listp (cons a xs))
         (and (rationalp a) (rational-listp xs)))
  :hints (("Goal" :in-theory (enable rational-listp))))

(defthm rational-listp-of-generated-tc-post-row-from-bank
  (implies
   (and (natp count)
        (natp point)
        (natp m)
        (<= (+ point count) m)
        (natp n)
        (natp out))
   (rational-listp
    (tc-post-row-from-bank
     n out (tc-lagrange-bank-aux count point m))))
  :hints
  (("Goal"
    :induct (tc-lagrange-bank-aux count point m)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-lagrange-bank-aux)
       tc-lagrange-bank-aux-when-zp
       tc-lagrange-bank-aux-open
       tc-post-row-from-bank-of-nil
       tc-post-row-from-bank-of-cons
       tc-current-point-below-bound
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-nfix-when-natp
       tc-rationalp-of-generated-post-head
       tc-rational-listp-of-cons
       rational-listp)))
   ("Subgoal *1/2"
    :use ((:instance tc-rationalp-of-generated-post-head)))))

(defthm len-of-tc-post-row
  (implies (posp n)
           (equal (len (tc-post-row n out))
                  (1- (* 2 n))))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-post-row)
       (:definition tc-lagrange-bank)
       len-of-tc-post-row-from-bank
       len-of-tc-lagrange-bank-aux
       tc-natp-of-generated-rank
       tc-nfix-when-natp)))))

(defthm rational-listp-of-tc-post-row
  (implies (and (posp n)
                (natp out))
           (rational-listp (tc-post-row n out)))
  :hints
  (("Goal"
    :use
    ((:instance rational-listp-of-generated-tc-post-row-from-bank
                (count (1- (* 2 n)))
                (point 0)
                (m (1- (* 2 n)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-post-row)
       (:definition tc-lagrange-bank)
       tc-natp-of-generated-rank
       tc-natp-from-posp
       tc-natp-of-zero)))))

(defthm tc-post-moments-okp-aux-when-zp
  (implies (zp count)
           (tc-post-moments-okp-aux count degree n out post))
  :hints
  (("Goal"
    :expand ((tc-post-moments-okp-aux count degree n out post))
    :in-theory (theory 'minimal-theory))))

(defthm tc-post-moments-okp-aux-open
  (implies
   (not (zp count))
   (equal
    (tc-post-moments-okp-aux count degree n out post)
    (and
     (equal (tc-row-moment post (nfix degree))
            (if (equal (mod (nfix degree) (nfix n))
                       (nfix out))
                1 0))
     (tc-post-moments-okp-aux
      (1- count) (1+ (nfix degree)) n out post))))
  :hints
  (("Goal"
    :expand ((tc-post-moments-okp-aux count degree n out post))
    :in-theory (theory 'minimal-theory))))

(defthm tc-post-moments-okp-aux-of-generated-post
  (implies
   (and (posp n)
        (natp out)
        (< out n)
        (natp count)
        (natp degree)
        (<= (+ degree count) (1- (* 2 n))))
   (tc-post-moments-okp-aux
    count degree n out (tc-post-row n out)))
  :hints
  (("Goal"
    :induct
    (tc-post-moments-okp-aux
     count degree n out (tc-post-row n out))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-post-moments-okp-aux)
       tc-post-moments-okp-aux-when-zp
       tc-post-moments-okp-aux-open
       tc-row-moment-of-generated-post
       tc-current-point-below-bound
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-nfix-when-natp
       tc-natp-from-posp
       tc-natp-of-generated-rank)))
   ("Subgoal *1/3"
    :use
    ((:instance tc-current-point-below-bound
                (point degree)
                (m (1- (* 2 n))))
     (:instance tc-row-moment-of-generated-post)))))

(defthm tc-post-moments-okp-of-generated-post
  (implies
   (and (posp n)
        (natp out)
        (< out n))
   (tc-post-moments-okp n out (tc-post-row n out)))
  :hints
  (("Goal"
    :use
    ((:instance tc-post-moments-okp-aux-of-generated-post
                (count (1- (* 2 n)))
                (degree 0)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-post-moments-okp)
       tc-natp-of-generated-rank
       tc-natp-of-zero)))))

(defthm tc-compact-post-certifiesp-of-generated-post
  (implies
   (and (posp n)
        (natp out)
        (< out n))
   (tc-compact-post-certifiesp n out (tc-post-row n out)))
  :hints
  (("Goal"
    :use
    ((:instance rational-listp-of-tc-post-row)
     (:instance len-of-tc-post-row)
     (:instance tc-post-moments-okp-of-generated-post))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-compact-post-certifiesp))))))

(defthm tc-post-row-from-generated-bank
  (implies
   (posp n)
   (equal
    (tc-post-row-from-bank
     n out (tc-lagrange-bank (1- (* 2 n))))
    (tc-post-row n out)))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-post-row))))))

(defthm tc-plan-posts-from-bank-when-zp
  (implies (zp count)
           (equal (tc-plan-posts-from-bank count out n bank) nil))
  :hints
  (("Goal"
    :expand ((tc-plan-posts-from-bank count out n bank))
    :in-theory (theory 'minimal-theory))))

(defthm tc-plan-posts-from-bank-open
  (implies
   (not (zp count))
   (equal
    (tc-plan-posts-from-bank count out n bank)
    (cons (tc-post-row-from-bank n (nfix out) bank)
          (tc-plan-posts-from-bank
           (1- count) (1+ (nfix out)) n bank))))
  :hints
  (("Goal"
    :expand ((tc-plan-posts-from-bank count out n bank))
    :in-theory (theory 'minimal-theory))))

(defthm tc-compact-bank-certifies-aux-when-zp
  (implies
   (zp count)
   (equal (tc-compact-bank-certifies-aux count out n posts)
          (endp posts)))
  :hints
  (("Goal"
    :expand ((tc-compact-bank-certifies-aux count out n posts))
    :in-theory (theory 'minimal-theory))))

(defthm tc-compact-bank-certifies-aux-open
  (implies
   (not (zp count))
   (equal
    (tc-compact-bank-certifies-aux count out n posts)
    (and (consp posts)
         (tc-compact-post-certifiesp n (nfix out) (car posts))
         (tc-compact-bank-certifies-aux
          (1- count) (1+ (nfix out)) n (cdr posts)))))
  :hints
  (("Goal"
    :expand ((tc-compact-bank-certifies-aux count out n posts))
    :in-theory (theory 'minimal-theory))))

(defthm tc-current-generated-post-certifies
  (implies
   (and (posp n)
        (natp count)
        (not (zp count))
        (natp out)
        (<= (+ out count) n))
   (tc-compact-post-certifiesp
    n out
    (tc-post-row-from-bank
     n out (tc-lagrange-bank (1- (* 2 n))))))
  :hints
  (("Goal"
    :use
    ((:instance tc-current-point-below-bound
                (point out) (m n))
     (:instance tc-compact-post-certifiesp-of-generated-post))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(tc-natp-from-posp
       tc-post-row-from-generated-bank)))))

(defthm tc-compact-bank-certifies-aux-of-generated-posts
  (implies
   (and (posp n)
        (natp count)
        (natp out)
        (<= (+ out count) n))
   (tc-compact-bank-certifies-aux
    count out n
    (tc-plan-posts-from-bank
     count out n (tc-lagrange-bank (1- (* 2 n))))))
  :hints
  (("Goal"
    :induct
    (tc-plan-posts-from-bank
     count out n (tc-lagrange-bank (1- (* 2 n))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction tc-plan-posts-from-bank)
       tc-plan-posts-from-bank-when-zp
       tc-plan-posts-from-bank-open
       tc-compact-bank-certifies-aux-when-zp
       tc-compact-bank-certifies-aux-open
       tc-current-generated-post-certifies
       tc-successor-interval-bound
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-nfix-when-natp
       car-cons
       cdr-cons)))))

(defthm tc-generated-compact-certifiesp-universal
  (implies (posp n)
           (tc-generated-compact-certifiesp n))
  :hints
  (("Goal"
    :use
    ((:instance tc-compact-bank-certifies-aux-of-generated-posts
                (count n) (out 0)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-generated-compact-certifiesp)
       (:definition tc-plan-posts)
       tc-natp-from-posp
       tc-natp-of-zero)))))

(defthm tc-generated-plan-certifiesp-universal
  (implies (posp n)
           (tc-generated-plan-certifiesp n))
  :hints
  (("Goal"
    :use
    ((:instance tc-generated-compact-certifiesp-universal)
     (:instance tc-generated-compact-certificate-implies-plan-certificate))
    :in-theory (theory 'minimal-theory))))

(defthm tc-generated-plan-correct-universal
  (implies
   (and (posp n)
        (qcx-vectorp n xs)
        (qcx-vectorp n ys))
   (equal (tc-run n xs ys)
          (wbc-cyclic-convolution n xs ys)))
  :hints
  (("Goal"
    :use
    ((:instance tc-generated-plan-certifiesp-universal)
     (:instance tc-generated-plan-correct))
    :in-theory (theory 'minimal-theory))))
