; Executable coefficient bounds for rational polynomial evaluation and
; secants.  These bounds turn a finite sign bracket into a quantitative
; rational endpoint certificate, without any appeal to real roots.
(in-package "ACL2")

(include-book "zck-stereographic-polynomial-closure")

(defun rts-poly-abs-bound (poly radius)
  (if (endp poly)
      0
    (+ (abs (car poly))
       (* (abs radius)
          (rts-poly-abs-bound (cdr poly) radius)))))

(defthm rationalp-of-rts-poly-abs-bound
  (implies (and (rational-listp poly)
                (rationalp radius))
           (rationalp (rts-poly-abs-bound poly radius)))
  :hints (("Goal"
           :induct (rts-poly-abs-bound poly radius)
           :in-theory (enable rts-poly-abs-bound rational-listp)))
  :rule-classes :type-prescription)

(defthm rts-poly-abs-bound-nonnegative
  (implies (and (rational-listp poly)
                (rationalp radius))
           (<= 0 (rts-poly-abs-bound poly radius)))
  :hints (("Goal"
           :induct (rts-poly-abs-bound poly radius)
           :in-theory (enable rts-poly-abs-bound rational-listp abs)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rts-abs-product
  (implies (and (rationalp x) (rationalp y))
           (equal (abs (* x y)) (* (abs x) (abs y))))
  :hints (("Goal"
           :cases ((< x 0) (< y 0))
           :in-theory (enable abs)
           :nonlinearp t)))

(defthm rts-abs-add-upper-bound
  (implies (and (rationalp x) (rationalp y))
           (<= (abs (+ x y)) (+ (abs x) (abs y))))
  :hints (("Goal"
           :cases ((< x 0) (< y 0) (< (+ x y) 0))
           :in-theory (enable abs)
           :nonlinearp t))
  :rule-classes :linear)

(defthm rationalp-of-rts-abs
  (implies (rationalp x)
           (rationalp (abs x)))
  :hints (("Goal" :in-theory (enable abs)))
  :rule-classes :type-prescription)

(defthm rts-abs-nonnegative
  (implies (rationalp x)
           (<= 0 (abs x)))
  :hints (("Goal" :in-theory (enable abs)))
  :rule-classes :linear)

(defthm rts-abs-zero
  (equal (abs 0) 0)
  :hints (("Goal" :in-theory (enable abs))))

(defthm rts-nonnegative-product-monotone
  (implies (and (rationalp a) (rationalp x) (rationalp y)
                (<= 0 a) (<= x y))
           (<= (* a x) (* a y)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm rts-abs-product-upper-rectangle
  (implies (and (rationalp x)
                (rationalp q)
                (rationalp radius)
                (rationalp bound)
                (<= 0 radius)
                (<= 0 bound)
                (<= (abs x) radius)
                (<= (abs q) bound))
           (<= (abs (* x q)) (* radius bound)))
  :hints
  (("Goal"
    :use ((:instance rts-abs-product (x x) (y q))
          (:instance rationalp-of-rts-abs (x x))
          (:instance rationalp-of-rts-abs (x q))
          (:instance rts-abs-nonnegative (x x))
          (:instance rts-abs-nonnegative (x q))
          (:instance rts-nonnegative-product-monotone
                     (a (abs x)) (x (abs q)) (y bound))
          (:instance rts-nonnegative-product-monotone
                     (a bound) (x (abs x)) (y radius)))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(commutativity-of-*)))))

(defthm rts-abs-product-upper-right
  (implies (and (rationalp x)
                (rationalp q)
                (rationalp bound)
                (<= 0 bound)
                (<= (abs q) bound))
           (<= (abs (* x q)) (* (abs x) bound)))
  :hints
  (("Goal"
    :use ((:instance rts-abs-product (x x) (y q))
          (:instance rationalp-of-rts-abs (x x))
          (:instance rationalp-of-rts-abs (x q))
          (:instance rts-abs-nonnegative (x x))
          (:instance rts-nonnegative-product-monotone
                     (a (abs x)) (x (abs q)) (y bound)))
    :in-theory (theory 'minimal-theory))))

(defthm rts-horner-abs-step
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp q)
                (rationalp radius)
                (rationalp bound)
                (<= 0 radius)
                (<= 0 bound)
                (<= (abs x) radius)
                (<= (abs q) bound))
           (<= (abs (+ a (* x q)))
               (+ (abs a) (* radius bound))))
  :hints
  (("Goal"
    :use ((:instance rts-abs-add-upper-bound (x a) (y (* x q)))
          (:instance rts-abs-product-upper-rectangle))
    :in-theory (theory 'minimal-theory))))

(defthm rts-poly-eval-abs-bound
  (implies (and (rational-listp poly)
                (rationalp x)
                (rationalp radius)
                (<= (abs x) (abs radius)))
           (<= (abs (tc-poly-eval poly x))
               (rts-poly-abs-bound poly radius)))
  :hints
  (("Goal"
    :induct (tc-poly-eval poly x)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(tc-poly-eval rts-poly-abs-bound rational-listp rts-abs-zero)))
   ("Subgoal *1/2"
    :use ((:instance rationalp-of-tc-poly-eval
                     (p (cdr poly)))
          (:instance rationalp-of-rts-poly-abs-bound
                     (poly (cdr poly)))
          (:instance rts-poly-abs-bound-nonnegative
                     (poly (cdr poly)))
          (:instance rationalp-of-rts-abs (x radius))
          (:instance rts-abs-nonnegative (x radius))
          (:instance rts-horner-abs-step
                     (a (car poly))
                     (q (tc-poly-eval (cdr poly) x))
                     (radius (abs radius))
                     (bound (rts-poly-abs-bound
                             (cdr poly) radius))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(tc-poly-eval rts-poly-abs-bound rational-listp rts-abs-zero)))))

(defthm rts-polynomial-secant-identity
  (implies (and (rational-listp poly)
                (rationalp x)
                (rationalp y))
           (equal (- (tc-poly-eval poly x)
                     (tc-poly-eval poly y))
                  (* (- x y)
                     (tc-poly-eval
                      (tc-poly-quotient-linear poly y) x))))
  :hints
  (("Goal"
    :use ((:instance tc-poly-eval-synthetic-division
                     (p poly) (root y)))
    :in-theory (theory 'minimal-theory))))

(defthm rts-polynomial-secant-abs-bound
  (implies (and (rational-listp poly)
                (rationalp x)
                (rationalp y)
                (rationalp radius)
                (<= (abs x) (abs radius)))
           (<= (abs (- (tc-poly-eval poly x)
                       (tc-poly-eval poly y)))
               (* (abs (- x y))
                  (rts-poly-abs-bound
                   (tc-poly-quotient-linear poly y)
                   radius))))
  :hints
  (("Goal"
    :use ((:instance rts-polynomial-secant-identity)
          (:instance rational-listp-of-tc-poly-quotient-linear
                     (p poly) (root y))
          (:instance rationalp-of-tc-poly-eval
                     (p (tc-poly-quotient-linear poly y))
                     (x x))
          (:instance rationalp-of-rts-poly-abs-bound
                     (poly (tc-poly-quotient-linear poly y)))
          (:instance rts-poly-abs-bound-nonnegative
                     (poly (tc-poly-quotient-linear poly y)))
          (:instance rts-poly-eval-abs-bound
                     (poly (tc-poly-quotient-linear poly y)))
          (:instance rts-abs-product-upper-right
                     (x (- x y))
                     (q (tc-poly-eval
                         (tc-poly-quotient-linear poly y) x))
                     (bound (rts-poly-abs-bound
                             (tc-poly-quotient-linear poly y)
                             radius))))
    :in-theory (theory 'minimal-theory))))
