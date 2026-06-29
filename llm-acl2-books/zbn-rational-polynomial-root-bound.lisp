; Rational polynomial evaluation, synthetic division, and a consecutive-root bound.
(in-package "ACL2")
(include-book "zbd-toom-cook-moment-certificate")
(include-book "arithmetic-5/top" :dir :system)


(defun tc-poly-eval (p x)
  (if (endp p)
      0
    (+ (car p) (* x (tc-poly-eval (cdr p) x)))))

(defun tc-zero-polyp (p)
  (if (endp p)
      t
    (and (equal (car p) 0)
         (tc-zero-polyp (cdr p)))))

(defun tc-poly-quotient-linear (p root)
  (if (endp (cdr p))
      nil
    (cons (tc-poly-eval (cdr p) root)
          (tc-poly-quotient-linear (cdr p) root))))

(defun tc-consecutive-rootsp (count start p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (tc-poly-eval p (nfix start)) 0)
         (tc-consecutive-rootsp (1- count) (1+ (nfix start)) p))))

(defthm rationalp-of-tc-poly-eval
  (implies (and (rational-listp p) (rationalp x))
           (rationalp (tc-poly-eval p x))))

(defthm tc-poly-eval-of-tc-poly-scale
  (implies (and (rational-listp p)
                (rationalp c)
                (rationalp x))
           (equal (tc-poly-eval (tc-poly-scale c p) x)
                  (* c (tc-poly-eval p x))))
  :hints (("Goal" :induct (tc-poly-scale c p)
           :in-theory (enable tc-poly-scale tc-poly-eval))))

(defthm tc-poly-eval-of-tc-poly-add
  (implies (and (rational-listp a)
                (rational-listp b)
                (rationalp x))
           (equal (tc-poly-eval (tc-poly-add a b) x)
                  (+ (tc-poly-eval a x)
                     (tc-poly-eval b x))))
  :hints (("Goal" :induct (tc-poly-add a b)
           :in-theory (enable tc-poly-add tc-poly-eval))))

(defthm tc-poly-eval-of-tc-poly-mul-linear
  (implies (and (rational-listp p)
                (rationalp root)
                (rationalp x))
           (equal (tc-poly-eval (tc-poly-mul-linear p root) x)
                  (* (- x root) (tc-poly-eval p x))))
  :hints (("Goal"
           :use ((:instance tc-poly-eval-of-tc-poly-add
                            (a (tc-poly-scale (- root) p))
                            (b (cons 0 p)))
                 (:instance tc-poly-eval-of-tc-poly-scale
                            (c (- root))))
           :in-theory (enable tc-poly-mul-linear tc-poly-eval))))

(defthm rational-listp-of-tc-poly-quotient-linear
  (implies (and (rational-listp p) (rationalp root))
           (rational-listp (tc-poly-quotient-linear p root)))
  :hints (("Goal" :induct (tc-poly-quotient-linear p root)
           :in-theory (enable tc-poly-quotient-linear))))

(defthm len-of-tc-poly-quotient-linear
  (equal (len (tc-poly-quotient-linear p root))
         (if (consp p) (1- (len p)) 0))
  :hints (("Goal" :induct (tc-poly-quotient-linear p root)
           :in-theory (enable tc-poly-quotient-linear))))

(defthm tc-poly-eval-synthetic-division
  (implies (and (rational-listp p)
                (rationalp root)
                (rationalp x))
           (equal (tc-poly-eval p x)
                  (+ (tc-poly-eval p root)
                     (* (- x root)
                        (tc-poly-eval
                         (tc-poly-quotient-linear p root) x)))))
  :hints (("Goal" :induct (tc-poly-quotient-linear p root)
           :in-theory (enable tc-poly-quotient-linear tc-poly-eval))))

(defthm tc-root-transfers-to-linear-quotient
  (implies (and (rational-listp p)
                (rationalp root)
                (rationalp x)
                (not (equal x root))
                (equal (tc-poly-eval p root) 0)
                (equal (tc-poly-eval p x) 0))
           (equal (tc-poly-eval
                   (tc-poly-quotient-linear p root) x)
                  0))
  :hints (("Goal"
           :use ((:instance tc-poly-eval-synthetic-division))
           :in-theory (disable tc-poly-eval-synthetic-division))))

(defun tc-poly-tail-induct (p root)
  (if (endp p)
      root
    (tc-poly-tail-induct (cdr p) root)))

(defthm tc-zero-polyp-of-tc-poly-scale
  (implies (tc-zero-polyp p)
           (tc-zero-polyp (tc-poly-scale c p)))
  :hints (("Goal" :induct (tc-poly-scale c p)
           :in-theory (enable tc-poly-scale tc-zero-polyp))))

(defthm tc-zero-polyp-of-tc-poly-add
  (implies (and (tc-zero-polyp a)
                (tc-zero-polyp b))
           (tc-zero-polyp (tc-poly-add a b)))
  :hints (("Goal" :induct (tc-poly-add a b)
           :in-theory (enable tc-poly-add tc-zero-polyp))))

(defthm tc-zero-polyp-of-tc-poly-mul-linear
  (implies (tc-zero-polyp p)
           (tc-zero-polyp (tc-poly-mul-linear p root)))
  :hints (("Goal"
           :in-theory (enable tc-poly-mul-linear))))

(defthm tc-poly-eval-cdr-zero-from-zero-quotient
  (implies (tc-zero-polyp (tc-poly-quotient-linear p root))
           (equal (tc-poly-eval (cdr p) root) 0))
  :hints (("Goal" :cases ((consp (cdr p))))
          ("Subgoal 2"
           :expand ((tc-poly-quotient-linear p root)
                    (tc-zero-polyp
                     (tc-poly-quotient-linear p root))))
          ("Subgoal 1"
           :in-theory (enable tc-poly-eval))))

(defthm tc-zero-polyp-of-cdr-quotient
  (implies (tc-zero-polyp (tc-poly-quotient-linear p root))
           (tc-zero-polyp
            (tc-poly-quotient-linear (cdr p) root)))
  :hints (("Goal" :cases ((consp (cdr p))))
          ("Subgoal 2"
           :expand ((tc-poly-quotient-linear p root)
                    (tc-zero-polyp
                     (tc-poly-quotient-linear p root))))
          ("Subgoal 1"
           :in-theory (enable tc-poly-quotient-linear tc-zero-polyp))))

(defthm tc-car-zero-from-eval-and-tail-eval
  (implies (and (consp p)
                (rationalp (car p))
                (equal (tc-poly-eval p root) 0)
                (equal (tc-poly-eval (cdr p) root) 0))
           (equal (car p) 0))
  :hints (("Goal" :expand ((tc-poly-eval p root)))))

(defthm tc-zero-polyp-of-linear-quotient-and-root
  (implies (and (rational-listp p)
                (rationalp root)
                (tc-zero-polyp (tc-poly-quotient-linear p root))
                (equal (tc-poly-eval p root) 0))
           (tc-zero-polyp p))
  :hints (("Goal"
           :induct (tc-poly-tail-induct p root)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-poly-tail-induct)
              (:induction tc-poly-tail-induct)
              (:definition endp)
              (:definition rational-listp)
              (:definition tc-zero-polyp)
              tc-poly-eval-cdr-zero-from-zero-quotient
              tc-zero-polyp-of-cdr-quotient
              tc-car-zero-from-eval-and-tail-eval)))))

(defun tc-roots-quotient-induct (count start p root)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list start p root)
    (tc-roots-quotient-induct
     (1- count) (1+ start) p root)))

(defthm tc-rationalp-when-natp
  (implies (natp x) (rationalp x)))

(defthm tc-less-natural-implies-distinct
  (implies (and (natp a) (natp b) (< a b))
           (not (equal b a))))

(defthm tc-root-transfers-to-later-natural
  (implies (and (natp root)
                (natp x)
                (< root x)
                (rational-listp p)
                (equal (tc-poly-eval p root) 0)
                (equal (tc-poly-eval p x) 0))
           (equal (tc-poly-eval
                   (tc-poly-quotient-linear p root) x)
                  0))
  :hints (("Goal"
           :use ((:instance tc-root-transfers-to-linear-quotient)
                 (:instance tc-rationalp-when-natp (x root))
                 (:instance tc-rationalp-when-natp (x x))
                 (:instance tc-less-natural-implies-distinct
                            (a root) (b x)))
           :in-theory (theory 'minimal-theory))))

(defthm tc-consecutive-rootsp-open
  (implies (not (zp count))
           (equal (tc-consecutive-rootsp count start p)
                  (and (equal (tc-poly-eval p (nfix start)) 0)
                       (tc-consecutive-rootsp
                        (1- count) (1+ (nfix start)) p))))
  :hints (("Goal" :expand ((tc-consecutive-rootsp count start p)))))

(defthm tc-consecutive-rootsp-when-zp
  (implies (zp count)
           (tc-consecutive-rootsp count start p))
  :hints (("Goal" :expand ((tc-consecutive-rootsp count start p)))))

(defthm tc-nfix-when-natp
  (implies (natp x) (equal (nfix x) x)))

(defthm tc-natp-of-one-less-when-positive
  (implies (and (natp x) (not (zp x)))
           (natp (1- x))))

(defthm tc-natp-of-one-plus
  (implies (natp x) (natp (1+ x))))

(defthm tc-less-than-one-plus
  (implies (and (natp a) (natp b) (< a b))
           (< a (1+ b))))

(defthm tc-consecutive-rootsp-of-linear-quotient-general
  (implies (and (natp count)
                (natp root)
                (natp start)
                (< root start)
                (rational-listp p)
                (equal (tc-poly-eval p root) 0)
                (tc-consecutive-rootsp count start p))
           (tc-consecutive-rootsp
            count start (tc-poly-quotient-linear p root)))
  :hints (("Goal"
           :induct (tc-roots-quotient-induct count start p root)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:induction tc-roots-quotient-induct)
              tc-consecutive-rootsp-open
              tc-consecutive-rootsp-when-zp
              tc-nfix-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-less-than-one-plus
              tc-root-transfers-to-later-natural)))))

(defthm tc-less-than-own-one-plus
  (implies (natp x) (< x (1+ x))))

(defthm tc-not-zp-of-one-plus
  (implies (natp x) (not (zp (1+ x)))))

(defthm tc-one-less-of-one-plus
  (implies (natp x)
           (equal (1- (1+ x)) x)))

(defthm tc-consecutive-rootsp-of-linear-quotient
  (implies (and (natp count)
                (natp start)
                (rational-listp p)
                (tc-consecutive-rootsp (1+ count) start p))
           (tc-consecutive-rootsp
            count (1+ start)
            (tc-poly-quotient-linear p start)))
  :hints (("Goal"
           :use ((:instance
                  tc-consecutive-rootsp-of-linear-quotient-general
                  (root start)
                  (start (1+ start))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-consecutive-rootsp-open
              tc-nfix-when-natp
              tc-natp-of-one-plus
              tc-less-than-own-one-plus
              tc-not-zp-of-one-plus
              tc-one-less-of-one-plus)))))

(defthm tc-positive-natural-is-one-plus-predecessor
  (implies (and (natp x) (not (zp x)))
           (equal (1+ (1- x)) x)))

(defthm tc-first-consecutive-root
  (implies (and (natp count)
                (not (zp count))
                (natp start)
                (tc-consecutive-rootsp count start p))
           (equal (tc-poly-eval p start) 0))
  :hints (("Goal"
           :use ((:instance tc-consecutive-rootsp-open))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-nfix-when-natp)))))

(defthm tc-remaining-consecutive-roots
  (implies (and (natp count)
                (not (zp count))
                (natp start)
                (tc-consecutive-rootsp count start p))
           (tc-consecutive-rootsp (1- count) (1+ start) p))
  :hints (("Goal"
           :use ((:instance tc-consecutive-rootsp-open))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-nfix-when-natp)))))

(defthm tc-first-quotient-retains-remaining-roots
  (implies (and (natp count)
                (not (zp count))
                (natp start)
                (rational-listp p)
                (tc-consecutive-rootsp count start p))
           (tc-consecutive-rootsp
            (1- count) (1+ start)
            (tc-poly-quotient-linear p start)))
  :hints (("Goal"
           :use ((:instance
                  tc-consecutive-rootsp-of-linear-quotient
                  (count (1- count))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(tc-natp-of-one-less-when-positive
              tc-positive-natural-is-one-plus-predecessor)))))

(defthm tc-length-bound-of-linear-quotient
  (implies (and (natp count)
                (not (zp count))
                (consp p)
                (<= (len p) count))
           (<= (len (tc-poly-quotient-linear p root))
               (1- count)))
  :hints (("Goal"
           :use ((:instance len-of-tc-poly-quotient-linear))
           :in-theory (disable len-of-tc-poly-quotient-linear))))

(defthm tc-zero-polyp-when-len-at-most-zero
  (implies (<= (len p) 0)
           (tc-zero-polyp p))
  :hints (("Goal" :cases ((consp p))
           :in-theory (enable tc-zero-polyp))))

(defthm tc-zero-polyp-when-endp
  (implies (endp p)
           (tc-zero-polyp p))
  :hints (("Goal" :in-theory (enable tc-zero-polyp))))

(defthm tc-zero-polyp-at-zp-length-bound
  (implies (and (natp count)
                (zp count)
                (<= (len p) count))
           (tc-zero-polyp p))
  :hints (("Goal"
           :use ((:instance tc-zero-polyp-when-len-at-most-zero))
           :in-theory (disable tc-zero-polyp-when-len-at-most-zero))))

(defthm tc-zero-polyp-from-zero-first-quotient
  (implies (and (natp count)
                (not (zp count))
                (natp start)
                (rational-listp p)
                (tc-consecutive-rootsp count start p)
                (tc-zero-polyp
                 (tc-poly-quotient-linear p start)))
           (tc-zero-polyp p))
  :hints (("Goal"
           :use ((:instance tc-first-consecutive-root)
                 (:instance tc-rationalp-when-natp (x start))
                 (:instance tc-zero-polyp-of-linear-quotient-and-root
                            (root start)))
           :in-theory (theory 'minimal-theory))))

(defun tc-root-bound-induct (count start p)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp p))
      (list start p)
    (tc-root-bound-induct
     (1- count) (1+ (nfix start))
     (tc-poly-quotient-linear p (nfix start)))))

(defthm tc-consecutive-root-bound
  (implies (and (natp count)
                (natp start)
                (rational-listp p)
                (<= (len p) count)
                (tc-consecutive-rootsp count start p))
           (tc-zero-polyp p))
  :hints (("Goal"
           :induct (tc-root-bound-induct count start p)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition tc-root-bound-induct)
              (:induction tc-root-bound-induct)
              (:definition endp)
              (:definition rational-listp)
              tc-nfix-when-natp
              tc-natp-of-one-less-when-positive
              tc-natp-of-one-plus
              tc-rationalp-when-natp
              rational-listp-of-tc-poly-quotient-linear
              tc-first-consecutive-root
              tc-first-quotient-retains-remaining-roots
              tc-length-bound-of-linear-quotient
              tc-zero-polyp-when-endp
              tc-zero-polyp-at-zp-length-bound
              tc-zero-polyp-from-zero-first-quotient)))))
