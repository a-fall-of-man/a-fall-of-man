; Finite rational certificates for arbitrary-dimensional not-a-knot cubics.
; Ordinary ACL2 only: no real numbers, limits, derivatives, or ACL2(r).
(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(include-book "std/lists/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Scalar cubic pieces in local coordinates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qnak-cubicp (p)
  (and (true-listp p)
       (equal (len p) 4)
       (rational-listp p)))

(defun qnak-cubic-listp (pieces)
  (if (consp pieces)
      (and (qnak-cubicp (car pieces))
           (qnak-cubic-listp (cdr pieces)))
    (equal pieces nil)))

(defun qnak-rational-fix (x)
  (if (rationalp x) x 0))

(defun qnak-cubic-eval (p u)
  (let ((u (qnak-rational-fix u)))
    (+ (qnak-rational-fix (car p))
       (* u (+ (qnak-rational-fix (cadr p))
               (* u (+ (qnak-rational-fix (caddr p))
                       (* u (qnak-rational-fix (cadddr p))))))))))

(defun qnak-cubic-d1 (p u)
  (let ((u (qnak-rational-fix u)))
    (+ (qnak-rational-fix (cadr p))
       (* 2 u (qnak-rational-fix (caddr p)))
       (* 3 u u (qnak-rational-fix (cadddr p))))))

(defun qnak-cubic-d2 (p u)
  (let ((u (qnak-rational-fix u)))
    (+ (* 2 (qnak-rational-fix (caddr p)))
       (* 6 u (qnak-rational-fix (cadddr p))))))

(defun qnak-cubic-leading (p)
  (qnak-rational-fix (cadddr p)))

(defthm rationalp-of-qnak-rational-fix
  (rationalp (qnak-rational-fix x)))

(defthm qnak-rational-fix-when-rationalp
  (implies (rationalp x)
           (equal (qnak-rational-fix x) x)))

(defthm rationalp-of-qnak-cubic-eval
  (rationalp (qnak-cubic-eval p u)))

(defthm rationalp-of-qnak-cubic-d1
  (rationalp (qnak-cubic-d1 p u)))

(defthm rationalp-of-qnak-cubic-d2
  (rationalp (qnak-cubic-d2 p u)))

(defthm rationalp-of-qnak-cubic-leading
  (rationalp (qnak-cubic-leading p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rational knot schedules and finite algebraic spline certificates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qnak-strict-rational-knots-p (knots)
  (if (consp knots)
      (and (rationalp (car knots))
           (or (endp (cdr knots))
               (and (< (car knots) (cadr knots))
                    (qnak-strict-rational-knots-p (cdr knots)))))
    (equal knots nil)))

(defun qnak-interpolation-closep (eps knots values pieces)
  (if (consp pieces)
      (and (consp knots)
           (consp (cdr knots))
           (consp values)
           (consp (cdr values))
           (let ((h (- (cadr knots) (car knots))))
             (and (<= (abs (- (qnak-cubic-eval (car pieces) 0)
                              (car values)))
                      eps)
                  (<= (abs (- (qnak-cubic-eval (car pieces) h)
                              (cadr values)))
                      eps)))
           (qnak-interpolation-closep eps
                                      (cdr knots)
                                      (cdr values)
                                      (cdr pieces)))
    t))

(defun qnak-c2-joinsp (knots pieces)
  (if (and (consp pieces)
           (consp (cdr pieces)))
      (and (consp knots)
           (consp (cdr knots))
           (let ((h (- (cadr knots) (car knots))))
             (and (equal (qnak-cubic-eval (car pieces) h)
                         (qnak-cubic-eval (cadr pieces) 0))
                  (equal (qnak-cubic-d1 (car pieces) h)
                         (qnak-cubic-d1 (cadr pieces) 0))
                  (equal (qnak-cubic-d2 (car pieces) h)
                         (qnak-cubic-d2 (cadr pieces) 0))))
           (qnak-c2-joinsp (cdr knots) (cdr pieces)))
    t))

(defun qnak-front-not-a-knot-p (pieces)
  (and (consp pieces)
       (consp (cdr pieces))
       (equal (qnak-cubic-leading (car pieces))
              (qnak-cubic-leading (cadr pieces)))))

(defun qnak-back-not-a-knot-p (pieces)
  (if (and (consp pieces)
           (consp (cdr pieces)))
      (if (endp (cddr pieces))
          (equal (qnak-cubic-leading (car pieces))
                 (qnak-cubic-leading (cadr pieces)))
        (qnak-back-not-a-knot-p (cdr pieces)))
    nil))

(defun qnak-scalar-certificatep (eps knots values pieces)
  (and (rationalp eps)
       (<= 0 eps)
       (<= 4 (len knots))
       (qnak-strict-rational-knots-p knots)
       (rational-listp values)
       (equal (len values) (len knots))
       (qnak-cubic-listp pieces)
       (equal (+ 1 (len pieces)) (len knots))
       (qnak-interpolation-closep eps knots values pieces)
       (qnak-c2-joinsp knots pieces)
       (qnak-front-not-a-knot-p pieces)
       (qnak-back-not-a-knot-p pieces)))

(defthm qnak-scalar-certificatep-implies-rational-cubics
  (implies (qnak-scalar-certificatep eps knots values pieces)
           (qnak-cubic-listp pieces)))

(defthm qnak-scalar-certificatep-implies-not-a-knot
  (implies (qnak-scalar-certificatep eps knots values pieces)
           (and (qnak-front-not-a-knot-p pieces)
                (qnak-back-not-a-knot-p pieces))))

(defthm qnak-scalar-certificatep-implies-c2
  (implies (qnak-scalar-certificatep eps knots values pieces)
           (qnak-c2-joinsp knots pieces)))

(defthm qnak-scalar-certificatep-implies-approximate-interpolation
  (implies (qnak-scalar-certificatep eps knots values pieces)
           (qnak-interpolation-closep eps knots values pieces)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Coordinate-major arbitrary-dimensional lift.
;;
;; VALUES-BY-COORDINATE and PIECES-BY-COORDINATE have one entry per
;; coordinate.  No dimension is fixed in the logic.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun qnak-coordinate-certificatesp
  (eps knots values-by-coordinate pieces-by-coordinate)
  (if (consp values-by-coordinate)
      (and (consp pieces-by-coordinate)
           (qnak-scalar-certificatep eps
                                     knots
                                     (car values-by-coordinate)
                                     (car pieces-by-coordinate))
           (qnak-coordinate-certificatesp eps
                                     knots
                                     (cdr values-by-coordinate)
                                     (cdr pieces-by-coordinate)))
    (and (equal values-by-coordinate nil)
         (equal pieces-by-coordinate nil))))

(defun qnak-vector-not-a-knot-p
  (values-by-coordinate pieces-by-coordinate)
  (if (consp values-by-coordinate)
      (and (consp pieces-by-coordinate)
           (qnak-front-not-a-knot-p (car pieces-by-coordinate))
           (qnak-back-not-a-knot-p (car pieces-by-coordinate))
           (qnak-vector-not-a-knot-p
            (cdr values-by-coordinate)
            (cdr pieces-by-coordinate)))
    (and (equal values-by-coordinate nil)
         (equal pieces-by-coordinate nil))))

(defun qnak-vector-c2-p
  (knots values-by-coordinate pieces-by-coordinate)
  (if (consp values-by-coordinate)
      (and (consp pieces-by-coordinate)
           (qnak-c2-joinsp knots (car pieces-by-coordinate))
           (qnak-vector-c2-p knots
                             (cdr values-by-coordinate)
                             (cdr pieces-by-coordinate)))
    (and (equal values-by-coordinate nil)
         (equal pieces-by-coordinate nil))))

(defun qnak-vector-interpolation-closep
  (eps knots values-by-coordinate pieces-by-coordinate)
  (if (consp values-by-coordinate)
      (and (consp pieces-by-coordinate)
           (qnak-interpolation-closep eps
                                      knots
                                      (car values-by-coordinate)
                                      (car pieces-by-coordinate))
           (qnak-vector-interpolation-closep
            eps knots
            (cdr values-by-coordinate)
            (cdr pieces-by-coordinate)))
    (endp pieces-by-coordinate)))

(defun qnak-vector-certificatep
  (eps knots values-by-coordinate pieces-by-coordinate)
  (and (qnak-coordinate-certificatesp
        eps knots values-by-coordinate pieces-by-coordinate)
       (qnak-vector-not-a-knot-p
        values-by-coordinate pieces-by-coordinate)
       (qnak-vector-c2-p
        knots values-by-coordinate pieces-by-coordinate)
       (qnak-vector-interpolation-closep
        eps knots values-by-coordinate pieces-by-coordinate)))

(defun qnak-vector-eval (pieces-by-coordinate segment u)
  (if (consp pieces-by-coordinate)
      (cons (qnak-cubic-eval
             (nth (nfix segment) (car pieces-by-coordinate))
             u)
            (qnak-vector-eval (cdr pieces-by-coordinate) segment u))
    nil))

(defun qnak-two-coordinate-list-induct (xs ys)
  (if (or (endp xs) (endp ys))
      nil
    (qnak-two-coordinate-list-induct (cdr xs) (cdr ys))))

(defthm len-of-qnak-vector-eval
  (equal (len (qnak-vector-eval pieces-by-coordinate segment u))
         (len pieces-by-coordinate)))

(defthm qnak-coordinate-certificatesp-dimensions-agree
  (implies (qnak-coordinate-certificatesp
            eps knots values-by-coordinate pieces-by-coordinate)
           (equal (len values-by-coordinate)
                  (len pieces-by-coordinate)))
  :hints (("Goal"
           :induct (qnak-two-coordinate-list-induct
                    values-by-coordinate pieces-by-coordinate)
           :in-theory (e/d (qnak-coordinate-certificatesp
                             qnak-two-coordinate-list-induct)
                            (qnak-scalar-certificatep)))))

(defthm qnak-vector-certificatep-dimensions-agree
  (implies (qnak-vector-certificatep
            eps knots values-by-coordinate pieces-by-coordinate)
           (equal (len values-by-coordinate)
                  (len pieces-by-coordinate)))
  :hints (("Goal"
           :use ((:instance qnak-coordinate-certificatesp-dimensions-agree))
           :in-theory (enable qnak-vector-certificatep))))

(defthm qnak-vector-certificatep-implies-not-a-knot
  (implies (qnak-vector-certificatep
            eps knots values-by-coordinate pieces-by-coordinate)
           (qnak-vector-not-a-knot-p
            values-by-coordinate pieces-by-coordinate))
  :hints (("Goal" :in-theory (enable qnak-vector-certificatep))))

(defthm qnak-vector-certificatep-implies-c2
  (implies (qnak-vector-certificatep
            eps knots values-by-coordinate pieces-by-coordinate)
           (qnak-vector-c2-p
            knots values-by-coordinate pieces-by-coordinate))
  :hints (("Goal" :in-theory (enable qnak-vector-certificatep))))

(defthm qnak-vector-certificatep-implies-approximate-interpolation
  (implies (qnak-vector-certificatep
            eps knots values-by-coordinate pieces-by-coordinate)
           (qnak-vector-interpolation-closep
            eps knots values-by-coordinate pieces-by-coordinate))
  :hints (("Goal" :in-theory (enable qnak-vector-certificatep))))

(defthm qnak-cubicp-of-nth
  (implies (and (qnak-cubic-listp pieces)
                (natp segment)
                (< segment (len pieces)))
           (qnak-cubicp (nth segment pieces)))
  :hints (("Goal" :induct (nth segment pieces)
                   :in-theory (enable qnak-cubic-listp))))

(defthm rational-listp-of-qnak-vector-eval
  (rational-listp
   (qnak-vector-eval pieces-by-coordinate segment u))
  :hints (("Goal"
           :induct (qnak-vector-eval pieces-by-coordinate segment u)
           :in-theory (enable qnak-vector-eval))))

(defthm nth-of-qnak-vector-eval
  (implies (and (natp coordinate)
                (< coordinate (len pieces-by-coordinate)))
           (equal (nth coordinate
                       (qnak-vector-eval
                        pieces-by-coordinate segment u))
                  (qnak-cubic-eval
                   (nth (nfix segment)
                        (nth coordinate pieces-by-coordinate))
                   u)))
  :hints (("Goal"
           :induct (nth coordinate pieces-by-coordinate)
           :in-theory (e/d (qnak-vector-eval)
                            (qnak-cubic-eval
                             qnak-rational-fix)))))

(defthm qnak-vector-eval-is-arbitrary-dimensional-rational
  (implies (qnak-vector-certificatep
            eps knots values-by-coordinate pieces-by-coordinate)
           (and (rational-listp
                 (qnak-vector-eval pieces-by-coordinate segment u))
                (equal (len (qnak-vector-eval
                             pieces-by-coordinate segment u))
                       (len values-by-coordinate))))
  :hints (("Goal"
           :use ((:instance qnak-vector-certificatep-dimensions-agree))
           :in-theory (disable qnak-vector-certificatep
                               qnak-vector-eval))))
