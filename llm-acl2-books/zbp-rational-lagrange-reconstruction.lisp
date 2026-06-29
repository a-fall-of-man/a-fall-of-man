; Coefficient-level reconstruction by the generated rational Lagrange basis.
(in-package "ACL2")
(include-book "zbo-rational-lagrange-interpolation")
(include-book "arithmetic-5/top" :dir :system)

(defun tc-lagrange-reconstruct-aux (count point m p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (tc-poly-add
     (tc-poly-scale
      (tc-poly-eval p (nfix point))
      (tc-lagrange-row m (nfix point)))
     (tc-lagrange-reconstruct-aux
      (1- count) (1+ (nfix point)) m p))))

(defun tc-lagrange-reconstruct (m p)
  (tc-lagrange-reconstruct-aux m 0 m p))

(defun tc-lagrange-sum-aux (count point m p x)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (* (tc-poly-eval p (nfix point))
          (tc-poly-eval
           (tc-lagrange-row m (nfix point)) x))
       (tc-lagrange-sum-aux
        (1- count) (1+ (nfix point)) m p x))))

(defthm tc-lagrange-reconstruct-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-reconstruct-aux count point m p)
                  nil))
  :hints (("Goal"
           :expand ((tc-lagrange-reconstruct-aux
                     count point m p)))))

(defthm tc-lagrange-reconstruct-aux-open
  (implies (not (zp count))
           (equal (tc-lagrange-reconstruct-aux count point m p)
                  (tc-poly-add
                   (tc-poly-scale
                    (tc-poly-eval p (nfix point))
                    (tc-lagrange-row m (nfix point)))
                   (tc-lagrange-reconstruct-aux
                    (1- count) (1+ (nfix point)) m p))))
  :hints (("Goal"
           :expand ((tc-lagrange-reconstruct-aux
                     count point m p)))))

(defthm tc-rational-listp-of-nil
  (rational-listp nil))

(defthm tc-current-point-below-bound
  (implies (and (natp count)
                (not (zp count))
                (natp point)
                (natp m)
                (<= (+ point count) m))
           (< point m)))

(defthm tc-successor-interval-bound
  (implies (and (natp count)
                (not (zp count))
                (natp point)
                (natp m)
                (<= (+ point count) m))
           (<= (+ (1+ point) (1- count)) m)))

(defthm rational-listp-of-tc-lagrange-reconstruct-aux
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (rational-listp p))
           (rational-listp
            (tc-lagrange-reconstruct-aux count point m p)))
  :hints (("Goal"
           :induct (tc-lagrange-reconstruct-aux count point m p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-reconstruct-aux)
              tc-lagrange-reconstruct-aux-when-zp
              tc-lagrange-reconstruct-aux-open
              tc-rational-listp-of-nil
              tc-nfix-when-natp
              tc-rationalp-of-nfix
              tc-rationalp-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-current-point-below-bound
              tc-successor-interval-bound
              rationalp-of-tc-poly-eval
              rational-listp-of-tc-lagrange-row
              rational-listp-of-tc-poly-scale
              rational-listp-of-tc-poly-add)))))

(defthm tc-max-with-zero-or-self
  (implies (natp m)
           (equal (max m (if test 0 m)) m)))

(defthm tc-max-self
  (equal (max m m) m))

(defthm tc-max-zero-right
  (implies (natp m)
           (equal (max m 0) m)))

(defthm tc-len-of-nil
  (equal (len nil) 0))

(defthm len-of-tc-lagrange-reconstruct-aux
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m))
           (equal (len (tc-lagrange-reconstruct-aux
                        count point m p))
                  (if (zp count) 0 m)))
  :hints (("Goal"
           :induct (tc-lagrange-reconstruct-aux count point m p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-reconstruct-aux)
              tc-lagrange-reconstruct-aux-when-zp
              tc-lagrange-reconstruct-aux-open
              tc-nfix-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-current-point-below-bound
              tc-successor-interval-bound
              len-of-tc-poly-add
              len-of-tc-poly-scale
              len-of-tc-lagrange-row
              tc-max-with-zero-or-self
              tc-max-self
              tc-max-zero-right
              tc-len-of-nil)))))

(defthm tc-lagrange-sum-aux-when-zp
  (implies (zp count)
           (equal (tc-lagrange-sum-aux count point m p x) 0))
  :hints (("Goal"
           :expand ((tc-lagrange-sum-aux count point m p x)))))

(defthm tc-lagrange-sum-aux-open
  (implies (not (zp count))
           (equal (tc-lagrange-sum-aux count point m p x)
                  (+ (* (tc-poly-eval p (nfix point))
                        (tc-poly-eval
                         (tc-lagrange-row m (nfix point)) x))
                     (tc-lagrange-sum-aux
                      (1- count) (1+ (nfix point)) m p x))))
  :hints (("Goal"
           :expand ((tc-lagrange-sum-aux count point m p x)))))

(defthm tc-poly-eval-of-nil
  (equal (tc-poly-eval nil x) 0)
  :hints (("Goal" :in-theory (enable tc-poly-eval))))

(defthm tc-poly-eval-of-lagrange-reconstruct-aux
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (rational-listp p)
                (rationalp x))
           (equal (tc-poly-eval
                   (tc-lagrange-reconstruct-aux count point m p) x)
                  (tc-lagrange-sum-aux count point m p x)))
  :hints (("Goal"
           :induct (tc-lagrange-reconstruct-aux count point m p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-reconstruct-aux)
              tc-lagrange-reconstruct-aux-when-zp
              tc-lagrange-reconstruct-aux-open
              tc-lagrange-sum-aux-when-zp
              tc-lagrange-sum-aux-open
              tc-poly-eval-of-nil
              tc-nfix-when-natp
              tc-rationalp-of-nfix
              tc-rationalp-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-current-point-below-bound
              tc-successor-interval-bound
              rationalp-of-tc-poly-eval
              rational-listp-of-tc-lagrange-row
              rational-listp-of-tc-poly-scale
              rational-listp-of-tc-lagrange-reconstruct-aux
              tc-poly-eval-of-tc-poly-scale
              tc-poly-eval-of-tc-poly-add)))))

(defthm tc-successor-interval-end
  (implies (and (natp count)
                (not (zp count))
                (natp point))
           (equal (+ (1+ point) (1- count))
                  (+ point count))))

(defthm tc-node-before-current-implies-before-bound
  (implies (and (natp point)
                (natp m)
                (< point m)
                (natp x)
                (< x point))
           (< x m)))

(defthm tc-node-before-successor
  (implies (and (natp point)
                (natp x)
                (< x point))
           (< x (1+ point))))

(defthm tc-lagrange-sum-aux-zero-before-interval
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (natp x)
                (< x point))
           (equal (tc-lagrange-sum-aux count point m p x)
                  0))
  :hints (("Goal"
           :induct (tc-lagrange-sum-aux count point m p x)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-sum-aux)
              tc-lagrange-sum-aux-when-zp
              tc-lagrange-sum-aux-open
              tc-nfix-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-current-point-below-bound
              tc-successor-interval-bound
              tc-node-before-current-implies-before-bound
              tc-node-before-successor
              tc-poly-eval-of-lagrange-row
              tc-times-zero)))))

(defthm tc-strict-successor-from-ordered-distinct
  (implies (and (natp point)
                (natp x)
                (<= point x)
                (not (equal point x)))
           (<= (1+ point) x)))

(defthm tc-count-positive-from-node-in-interval
  (implies (and (natp count)
                (natp point)
                (natp x)
                (<= point x)
                (< x (+ point count)))
           (not (zp count))))

(defthm tc-times-one-plus-zero
  (implies (acl2-numberp a)
           (equal (+ (* a 1) 0) a)))

(defthm tc-poly-eval-times-one-plus-zero-at-natural
  (implies (and (rational-listp p)
                (natp x))
           (equal (+ (* (tc-poly-eval p x) 1) 0)
                  (tc-poly-eval p x)))
  :hints (("Goal"
           :use ((:instance rationalp-of-tc-poly-eval)
                 (:instance tc-rationalp-when-natp)
                 (:instance tc-times-one-plus-zero
                            (a (tc-poly-eval p x))))
           :in-theory (theory 'minimal-theory))))

(defthm tc-acl2-numberp-of-poly-eval-at-natural
  (implies (and (rational-listp p)
                (natp x))
           (acl2-numberp (tc-poly-eval p x)))
  :hints (("Goal"
           :use ((:instance rationalp-of-tc-poly-eval)
                 (:instance tc-rationalp-when-natp)))))

(defthm tc-lagrange-sum-aux-selects-node
  (implies (and (natp count)
                (natp point)
                (natp m)
                (<= (+ point count) m)
                (natp x)
                (<= point x)
                (< x (+ point count))
                (rational-listp p))
           (equal (tc-lagrange-sum-aux count point m p x)
                  (tc-poly-eval p x)))
  :hints (("Goal"
           :induct (tc-lagrange-sum-aux count point m p x)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-lagrange-sum-aux)
              tc-lagrange-sum-aux-when-zp
              tc-lagrange-sum-aux-open
              tc-nfix-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-current-point-below-bound
              tc-successor-interval-bound
              tc-successor-interval-end
              tc-count-positive-from-node-in-interval
              tc-strict-successor-from-ordered-distinct
              tc-lagrange-sum-aux-zero-before-interval
              tc-poly-eval-of-lagrange-row
              rationalp-of-tc-poly-eval
              tc-rationalp-when-natp
              tc-times-one-plus-zero
              tc-poly-eval-times-one-plus-zero-at-natural
              tc-acl2-numberp-of-poly-eval-at-natural)))
          ("Subgoal *1/1"
           :cases ((equal x point)))))

(defthm tc-natp-is-at-least-zero
  (implies (natp x)
           (<= 0 x)))

(defthm tc-self-sum-bound
  (implies (natp m)
           (<= (+ 0 m) m)))

(defthm tc-poly-eval-of-lagrange-reconstruct-at-node
  (implies (and (natp m)
                (natp x)
                (< x m)
                (rational-listp p))
           (equal (tc-poly-eval (tc-lagrange-reconstruct m p) x)
                  (tc-poly-eval p x)))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-lagrange-reconstruct-aux
                  (count m) (point 0))
                 (:instance
                  tc-lagrange-sum-aux-selects-node
                  (count m) (point 0)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-lagrange-reconstruct)
              tc-natp-of-zero
              tc-natp-is-at-least-zero
              tc-self-sum-bound
              tc-rationalp-when-natp)))))

(defthm rational-listp-of-tc-lagrange-reconstruct
  (implies (and (natp m)
                (rational-listp p))
           (rational-listp (tc-lagrange-reconstruct m p)))
  :hints (("Goal"
           :use ((:instance
                  rational-listp-of-tc-lagrange-reconstruct-aux
                  (count m) (point 0)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-lagrange-reconstruct)
              tc-natp-of-zero
              tc-self-sum-bound)))))

(defthm tc-zp-natural-is-zero
  (implies (and (natp m)
                (zp m))
           (equal m 0))
  :rule-classes nil)

(defthm len-of-tc-lagrange-reconstruct
  (implies (natp m)
           (equal (len (tc-lagrange-reconstruct m p)) m))
  :hints (("Goal"
           :use ((:instance
                  len-of-tc-lagrange-reconstruct-aux
                  (count m) (point 0))
                 (:instance tc-zp-natural-is-zero))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-lagrange-reconstruct)
              tc-natp-of-zero
              tc-self-sum-bound)))))

(defun tc-poly-difference (a b)
  (if (endp a)
      nil
    (cons (- (car a) (car b))
          (tc-poly-difference (cdr a) (cdr b)))))

(defthm len-of-tc-poly-difference
  (equal (len (tc-poly-difference a b))
         (len a))
  :hints (("Goal"
           :induct (tc-poly-difference a b)
           :in-theory (enable tc-poly-difference))))

(defthm rational-listp-of-tc-poly-difference
  (implies (and (rational-listp a)
                (rational-listp b)
                (equal (len a) (len b)))
           (rational-listp (tc-poly-difference a b)))
  :hints (("Goal"
           :induct (tc-poly-difference a b)
           :in-theory (enable tc-poly-difference))))

(defthm tc-poly-difference-as-add-scale
  (implies (equal (len a) (len b))
           (equal (tc-poly-difference a b)
                  (tc-poly-add a (tc-poly-scale -1 b))))
  :hints (("Goal"
           :induct (tc-poly-difference a b)
           :in-theory (enable tc-poly-difference
                              tc-poly-add
                              tc-poly-scale))))

(defthm tc-rational-minus-as-plus-negative-one
  (implies (and (rationalp a)
                (rationalp b))
           (equal (+ a (* -1 b))
                  (- a b))))

(defthm tc-poly-eval-of-tc-poly-difference
  (implies (and (rational-listp a)
                (rational-listp b)
                (equal (len a) (len b))
                (rationalp x))
           (equal (tc-poly-eval (tc-poly-difference a b) x)
                  (- (tc-poly-eval a x)
                     (tc-poly-eval b x))))
  :hints (("Goal"
           :use ((:instance tc-poly-difference-as-add-scale)
                 (:instance rational-listp-of-tc-poly-scale
                            (c -1) (p b))
                 (:instance tc-poly-eval-of-tc-poly-add
                            (a a) (b (tc-poly-scale -1 b)))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c -1) (p b))
                 (:instance rationalp-of-tc-poly-eval (p a))
                 (:instance rationalp-of-tc-poly-eval (p b))
                 (:instance tc-rational-minus-as-plus-negative-one
                            (a (tc-poly-eval a x))
                            (b (tc-poly-eval b x))))
           :in-theory (theory 'minimal-theory))))

(defthm tc-poly-difference-when-endp
  (implies (endp a)
           (equal (tc-poly-difference a b) nil))
  :hints (("Goal" :expand ((tc-poly-difference a b)))))

(defthm tc-poly-difference-open
  (implies (not (endp a))
           (equal (tc-poly-difference a b)
                  (cons (- (car a) (car b))
                        (tc-poly-difference (cdr a) (cdr b)))))
  :hints (("Goal" :expand ((tc-poly-difference a b)))))

(defthm tc-zero-polyp-of-cons
  (equal (tc-zero-polyp (cons x xs))
         (and (equal x 0)
              (tc-zero-polyp xs)))
  :hints (("Goal" :in-theory (enable tc-zero-polyp))))

(defthm tc-rational-difference-zero-iff-equal
  (implies (and (rationalp a)
                (rationalp b))
           (equal (equal (- a b) 0)
                  (equal a b))))

(defthm tc-zero-polyp-of-nil
  (tc-zero-polyp nil)
  :hints (("Goal" :in-theory (enable tc-zero-polyp))))

(defthm tc-consp-second-from-equal-length
  (implies (and (consp a)
                (equal (len a) (len b)))
           (consp b)))

(defthm tc-cdr-lengths-equal
  (implies (and (consp a)
                (consp b)
                (equal (len a) (len b)))
           (equal (len (cdr a))
                  (len (cdr b)))))

(defthm tc-equal-lists-from-components
  (implies (and (consp a)
                (consp b)
                (equal (car a) (car b))
                (equal (cdr a) (cdr b)))
           (equal a b))
  :hints (("Goal"
           :use ((:instance cons-car-cdr (x a))
                 (:instance cons-car-cdr (x b)))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm tc-zero-difference-step
  (implies (and (consp a)
                (consp b)
                (rational-listp a)
                (rational-listp b)
                (tc-zero-polyp (tc-poly-difference a b)))
           (and (equal (car a) (car b))
                (tc-zero-polyp
                 (tc-poly-difference (cdr a) (cdr b)))))
  :hints (("Goal"
           :use ((:instance tc-poly-difference-open)
                 (:instance tc-zero-polyp-of-cons
                            (x (- (car a) (car b)))
                            (xs (tc-poly-difference (cdr a) (cdr b))))
                 (:instance tc-rational-difference-zero-iff-equal
                            (a (car a))
                            (b (car b))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition rational-listp)))))
  :rule-classes nil)

(defun tc-list-pair-induct (a b)
  (if (endp a)
      b
    (tc-list-pair-induct (cdr a) (cdr b))))

(in-theory (disable tc-poly-difference-as-add-scale))

(defthm tc-zero-difference-induction-step
  (implies
   (and (consp a)
        (rational-listp a)
        (rational-listp b)
        (equal (len a) (len b))
        (tc-zero-polyp (tc-poly-difference a b))
        (implies
         (and (rational-listp (cdr a))
              (rational-listp (cdr b))
              (equal (len (cdr a)) (len (cdr b)))
              (tc-zero-polyp
               (tc-poly-difference (cdr a) (cdr b))))
         (equal (cdr a) (cdr b))))
   (equal a b))
  :hints (("Goal"
           :use ((:instance tc-consp-second-from-equal-length)
                 (:instance tc-cdr-lengths-equal)
                 (:instance tc-zero-difference-step)
                 (:instance tc-equal-lists-from-components))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition rational-listp)))))
  :rule-classes nil)

(defthm tc-consp-implies-len-not-zero
  (implies (consp x)
           (not (equal 0 (len x)))))

(defthm tc-zero-difference-induction-base
  (implies (and (endp a)
                (rational-listp a)
                (rational-listp b)
                (equal (len a) (len b)))
           (equal a b))
  :hints (("Goal"
           :cases ((consp b))
           :use ((:instance tc-consp-implies-len-not-zero (x b)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition endp)
              (:definition rational-listp)
              (:definition len)))))
  :rule-classes nil)

(defthm tc-zero-polyp-of-tc-poly-difference-implies-equal
  (implies (and (rational-listp a)
                (rational-listp b)
                (equal (len a) (len b))
                (tc-zero-polyp (tc-poly-difference a b)))
           (equal a b))
  :hints (("Goal"
           :induct (tc-list-pair-induct a b)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-list-pair-induct)
              (:definition endp))))
          ("Subgoal *1/2"
           :use ((:instance tc-zero-difference-induction-step))
           :in-theory (theory 'minimal-theory))
          ("Subgoal *1/1"
           :use ((:instance tc-zero-difference-induction-base))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm tc-reconstruction-difference-zero-at-node
  (implies (and (natp m)
                (natp x)
                (< x m)
                (rational-listp p)
                (equal (len p) m))
           (equal
            (tc-poly-eval
             (tc-poly-difference
              (tc-lagrange-reconstruct m p)
              p)
             x)
            0))
  :hints (("Goal"
           :use ((:instance
                  tc-poly-eval-of-lagrange-reconstruct-at-node)
                 (:instance
                  rational-listp-of-tc-lagrange-reconstruct)
                 (:instance
                  len-of-tc-lagrange-reconstruct)
                 (:instance
                  tc-poly-eval-of-tc-poly-difference
                  (a (tc-lagrange-reconstruct m p))
                  (b p))
                 (:instance tc-rationalp-when-natp (x x)))
           :in-theory (theory 'minimal-theory))))

(defun tc-interval-root-induct (count start)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      start
    (tc-interval-root-induct
     (1- count) (1+ (nfix start)))))

(defthm tc-consecutive-roots-of-reconstruction-difference
  (implies
   (and (natp count)
        (natp start)
        (natp m)
        (<= (+ start count) m)
        (rational-listp p)
        (equal (len p) m))
   (tc-consecutive-rootsp
    count start
    (tc-poly-difference
     (tc-lagrange-reconstruct m p)
     p)))
  :hints
  (("Goal"
    :induct (tc-interval-root-induct count start)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition tc-interval-root-induct)
       (:induction tc-interval-root-induct)
       tc-consecutive-rootsp-open
       tc-consecutive-rootsp-when-zp
       tc-nfix-when-natp
       tc-natp-of-one-less-when-positive
       tc-natp-of-one-plus
       tc-current-point-below-bound
       tc-successor-interval-bound
       tc-reconstruction-difference-zero-at-node)))))

(defthm tc-zero-polyp-of-lagrange-reconstruction-difference
  (implies
   (and (natp m)
        (rational-listp p)
        (equal (len p) m))
   (tc-zero-polyp
    (tc-poly-difference
     (tc-lagrange-reconstruct m p)
     p)))
  :hints
  (("Goal"
    :use
    ((:instance
      tc-consecutive-root-bound
      (count m)
      (start 0)
      (p (tc-poly-difference
          (tc-lagrange-reconstruct m p)
          p)))
     (:instance
      tc-consecutive-roots-of-reconstruction-difference
      (count m)
      (start 0))
     (:instance
      rational-listp-of-tc-lagrange-reconstruct)
     (:instance
      len-of-tc-lagrange-reconstruct)
     (:instance
      rational-listp-of-tc-poly-difference
      (a (tc-lagrange-reconstruct m p))
      (b p))
     (:instance
      len-of-tc-poly-difference
      (a (tc-lagrange-reconstruct m p))
      (b p))
     (:instance tc-natp-of-zero)
     (:instance tc-self-sum-bound))
    :in-theory (theory 'minimal-theory))))

(defthm tc-lagrange-reconstruction-coefficient-identity
  (implies (and (natp m)
                (rational-listp p)
                (equal (len p) m))
           (equal (tc-lagrange-reconstruct m p)
                  p))
  :hints
  (("Goal"
    :use
    ((:instance
      tc-zero-polyp-of-tc-poly-difference-implies-equal
      (a (tc-lagrange-reconstruct m p))
      (b p))
     (:instance
      tc-zero-polyp-of-lagrange-reconstruction-difference)
     (:instance
      rational-listp-of-tc-lagrange-reconstruct)
     (:instance
      len-of-tc-lagrange-reconstruct))
    :in-theory (theory 'minimal-theory))))
