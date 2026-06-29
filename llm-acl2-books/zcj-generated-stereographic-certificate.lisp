; Generated closure and proper-power separation certificates for rational
; stereographic twiddle seeds.  Ordinary ACL2, finite rational arithmetic.
(in-package "ACL2")

(include-book "zci-stereographic-power-polynomials")

(defun rts-min2 (x y)
  (if (<= x y) x y))

(defun rts-table-min-distance (table)
  (if (endp table)
      0
    (let ((here (qcx-dist (car table) (qcx-one))))
      (if (endp (cdr table))
          here
        (rts-min2 here (rts-table-min-distance (cdr table)))))))

(defun rts-proper-power-table (n seed)
  (rct-power-table-aux (1- (nfix n)) seed seed))

(defun rts-generated-separation (n seed)
  (/ (rts-table-min-distance (rts-proper-power-table n seed)) 2))

(defun rts-closure-error (n tangent)
  (qcx-dist
   (rct-advance n (qcx-one) (rct-rational-unit nil tangent))
   (qcx-one)))

(defun rts-generated-parameter-certificatep (n epsilon tangent)
  (let* ((seed (rct-rational-unit nil tangent))
         (minimum
          (rts-table-min-distance (rts-proper-power-table n seed))))
    (and (posp n)
         (rationalp epsilon)
         (<= 0 epsilon)
         (rationalp tangent)
         (<= (rts-closure-error n tangent) epsilon)
         (< 0 minimum))))

(defthm rts-min2-at-most-left
  (implies (and (rationalp x) (rationalp y))
           (<= (rts-min2 x y) x))
  :hints (("Goal" :in-theory (enable rts-min2)))
  :rule-classes :linear)

(defthm rts-min2-at-most-right
  (implies (and (rationalp x) (rationalp y))
           (<= (rts-min2 x y) y))
  :hints (("Goal" :in-theory (enable rts-min2)))
  :rule-classes :linear)

(defthm rationalp-of-rts-min2
  (implies (and (rationalp x) (rationalp y))
           (rationalp (rts-min2 x y)))
  :hints (("Goal" :in-theory (enable rts-min2)))
  :rule-classes :type-prescription)

(defthm qcx-list-rationalp-of-rct-power-table-aux-recalled
  (implies (and (qcx-rationalp current)
                (qcx-rationalp seed))
           (qcx-list-rationalp
            (rct-power-table-aux count current seed)))
  :hints (("Goal"
           :use ((:instance qcx-list-rationalp-of-rct-power-table-aux))
           :in-theory nil)))

(defthm rationalp-of-rts-table-min-distance
  (implies (qcx-list-rationalp table)
           (rationalp (rts-table-min-distance table)))
  :hints (("Goal"
           :induct (rts-table-min-distance table)
           :in-theory (enable rts-table-min-distance
                              qcx-list-rationalp)))
  :rule-classes :type-prescription)

(defthm rts-table-min-distance-nonnegative
  (<= 0 (rts-table-min-distance table))
  :hints (("Goal"
           :induct (rts-table-min-distance table)
           :in-theory (enable rts-table-min-distance rts-min2)))
  :rule-classes :linear)

(defthm rct-table-separated-from-one-p-monotone
  (implies (and (rationalp small)
                (rationalp large)
                (<= small large)
                (rct-table-separated-from-one-p large table))
           (rct-table-separated-from-one-p small table))
  :hints (("Goal"
           :induct (rct-table-separated-from-one-p large table)
           :in-theory (enable rct-table-separated-from-one-p))))

(defthm rts-minimum-positive-implies-head-separated
  (implies (and (consp table)
                (qcx-list-rationalp table)
                (< 0 (rts-table-min-distance table)))
           (< (/ (rts-table-min-distance table) 2)
              (qcx-dist (car table) (qcx-one))))
  :hints (("Goal"
           :cases ((endp (cdr table)))
           :use ((:instance rts-min2-at-most-left
                            (x (qcx-dist (car table) (qcx-one)))
                            (y (rts-table-min-distance (cdr table))))
                 (:instance rationalp-of-qcx-dist
                            (x (car table)) (y (qcx-one))))
           :in-theory (enable rts-table-min-distance
                              qcx-list-rationalp qcx-one qcx qcx-rationalp)))
  :rule-classes :linear)

(defthm rts-minimum-positive-implies-tail-minimum-positive
  (implies (and (consp (cdr table))
                (qcx-list-rationalp table)
                (< 0 (rts-table-min-distance table)))
           (< 0 (rts-table-min-distance (cdr table))))
  :hints (("Goal"
           :use ((:instance rts-min2-at-most-right
                            (x (qcx-dist (car table) (qcx-one)))
                            (y (rts-table-min-distance (cdr table))))
                 (:instance rationalp-of-qcx-dist
                            (x (car table)) (y (qcx-one))))
           :in-theory (enable rts-table-min-distance
                              qcx-list-rationalp qcx-one qcx qcx-rationalp)))
  :rule-classes :linear)

(defthm rts-minimum-half-at-most-tail-minimum-half
  (implies (and (consp (cdr table))
                (qcx-list-rationalp table))
           (<= (/ (rts-table-min-distance table) 2)
               (/ (rts-table-min-distance (cdr table)) 2)))
  :hints (("Goal"
           :use ((:instance rts-min2-at-most-right
                            (x (qcx-dist (car table) (qcx-one)))
                            (y (rts-table-min-distance (cdr table))))
                 (:instance rationalp-of-qcx-dist
                            (x (car table)) (y (qcx-one))))
           :in-theory (enable rts-table-min-distance
                              qcx-list-rationalp qcx-one qcx qcx-rationalp)))
  :rule-classes :linear)

(defthm rts-table-min-distance-of-nil
  (equal (rts-table-min-distance nil) 0)
  :hints (("Goal"
           :expand ((rts-table-min-distance nil))
           :in-theory (theory 'minimal-theory))))

(defthm rts-table-min-distance-when-not-consp
  (implies (not (consp table))
           (equal (rts-table-min-distance table) 0))
  :hints
  (("Goal"
    :expand ((rts-table-min-distance table))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(endp)))))

(defthm rts-table-min-distance-of-singleton
  (equal (rts-table-min-distance (list x))
         (qcx-dist x (qcx-one)))
  :hints (("Goal"
           :expand ((rts-table-min-distance (list x)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))

(defthm rts-table-min-distance-of-cons-with-tail
  (implies (consp tail)
           (equal (rts-table-min-distance (cons x tail))
                  (rts-min2 (qcx-dist x (qcx-one))
                            (rts-table-min-distance tail))))
  :hints (("Goal"
           :expand ((rts-table-min-distance (cons x tail)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))

(defthm rct-table-separated-from-one-p-of-nil
  (rct-table-separated-from-one-p separation nil)
  :hints (("Goal"
           :expand ((rct-table-separated-from-one-p separation nil))
           :in-theory (theory 'minimal-theory))))

(defthm rct-table-separated-from-one-p-of-cons
  (equal (rct-table-separated-from-one-p separation (cons x tail))
         (and (< separation (qcx-dist x (qcx-one)))
              (rct-table-separated-from-one-p separation tail)))
  :hints (("Goal"
           :expand ((rct-table-separated-from-one-p
                     separation (cons x tail)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(car-cons cdr-cons)))))

(defthm rct-table-separated-from-one-p-when-consp
  (implies (consp table)
           (equal (rct-table-separated-from-one-p separation table)
                  (and (< separation
                          (qcx-dist (car table) (qcx-one)))
                       (rct-table-separated-from-one-p
                        separation (cdr table)))))
  :hints
  (("Goal"
    :use ((:instance rct-table-separated-from-one-p-of-cons
                     (x (car table))
                     (tail (cdr table))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(cons-car-cdr)))))

(defun rts-table-separation-induct (table)
  (if (endp table)
      nil
    (if (endp (cdr table))
        table
      (rts-table-separation-induct (cdr table)))))

(defthm qcx-list-rationalp-of-cdr
  (implies (qcx-list-rationalp table)
           (qcx-list-rationalp (cdr table)))
  :hints (("Goal" :in-theory (enable qcx-list-rationalp))))

(defthm rts-tail-separated-at-whole-minimum-half
  (implies
   (and (consp (cdr table))
        (qcx-list-rationalp table)
        (rct-table-separated-from-one-p
         (/ (rts-table-min-distance (cdr table)) 2)
         (cdr table)))
   (rct-table-separated-from-one-p
    (/ (rts-table-min-distance table) 2)
    (cdr table)))
  :hints
  (("Goal"
    :use ((:instance rts-minimum-half-at-most-tail-minimum-half)
          (:instance rationalp-of-rts-table-min-distance
                     (table table))
          (:instance rationalp-of-rts-table-min-distance
                     (table (cdr table)))
          (:instance rct-table-separated-from-one-p-monotone
                     (small (/ (rts-table-min-distance table) 2))
                     (large (/ (rts-table-min-distance (cdr table)) 2))
                     (table (cdr table))))
    :in-theory '(qcx-list-rationalp-of-cdr))))

(defthm rts-minimum-generates-singleton-shaped-separation
  (implies (and (consp table)
                (not (consp (cdr table)))
                (qcx-list-rationalp table)
                (< 0 (rts-table-min-distance table)))
           (rct-table-separated-from-one-p
            (/ (rts-table-min-distance table) 2)
            table))
  :hints
  (("Goal"
    :use ((:instance rts-minimum-positive-implies-head-separated))
    :in-theory (enable rct-table-separated-from-one-p))))

(defthm rts-minimum-separation-cons-step
  (implies
   (and (consp table)
        (consp (cdr table))
        (qcx-list-rationalp table)
        (< 0 (rts-table-min-distance table))
        (rct-table-separated-from-one-p
         (/ (rts-table-min-distance (cdr table)) 2)
         (cdr table)))
   (rct-table-separated-from-one-p
    (/ (rts-table-min-distance table) 2)
    table))
  :hints
  (("Goal"
    :use ((:instance rts-minimum-positive-implies-head-separated)
          (:instance rts-tail-separated-at-whole-minimum-half))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rct-table-separated-from-one-p-when-consp)))))

(defthm rts-minimum-generates-table-separation
  (implies (and (qcx-list-rationalp table)
                (< 0 (rts-table-min-distance table)))
           (rct-table-separated-from-one-p
            (/ (rts-table-min-distance table) 2)
            table))
  :hints
  (("Goal"
    :induct (rts-table-separation-induct table)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rts-table-separation-induct)
       rts-table-min-distance-of-nil
       rts-table-min-distance-when-not-consp
       qcx-list-rationalp-of-cdr
       rts-minimum-positive-implies-tail-minimum-positive
       rts-minimum-generates-singleton-shaped-separation
       rts-minimum-separation-cons-step)))))

(defthm rct-separated-orbitp-from-generated-table
  (implies
   (rct-table-separated-from-one-p
    separation (rct-power-table-aux count current seed))
   (rct-separated-orbitp count current seed separation))
  :hints (("Goal"
           :induct (rct-power-table-aux count current seed)
           :in-theory (enable rct-power-table-aux
                              rct-separated-orbitp
                              rct-table-separated-from-one-p))))

(defthm qcx-list-rationalp-of-rts-proper-power-table
  (implies (qcx-rationalp seed)
           (qcx-list-rationalp (rts-proper-power-table n seed)))
  :hints (("Goal"
           :use ((:instance qcx-list-rationalp-of-rct-power-table-aux
                            (count (1- (nfix n)))
                            (current seed)))
           :in-theory (enable rts-proper-power-table))))

(defthm rts-generated-separation-is-rational
  (implies (qcx-rationalp seed)
           (rationalp (rts-generated-separation n seed)))
  :hints (("Goal"
           :use ((:instance rationalp-of-rts-table-min-distance
                            (table (rts-proper-power-table n seed))))
           :in-theory (enable rts-generated-separation)))
  :rule-classes :type-prescription)

(defthm rts-generated-separation-is-positive
  (implies
   (and (qcx-rationalp seed)
        (< 0 (rts-table-min-distance
              (rts-proper-power-table n seed))))
   (< 0 (rts-generated-separation n seed)))
  :hints (("Goal"
           :in-theory (enable rts-generated-separation)))
  :rule-classes :linear)

(defthm rts-generated-separation-certifies-proper-orbit
  (implies
   (and (qcx-rationalp seed)
        (< 0 (rts-table-min-distance
              (rts-proper-power-table n seed))))
   (rct-separated-orbitp
    (1- (nfix n)) seed seed (rts-generated-separation n seed)))
  :hints
  (("Goal"
    :use ((:instance rts-minimum-generates-table-separation
                     (table (rts-proper-power-table n seed)))
          (:instance rct-separated-orbitp-from-generated-table
                     (count (1- (nfix n)))
                     (current seed)
                     (separation (rts-generated-separation n seed))))
    :in-theory (enable rts-proper-power-table
                       rts-generated-separation))))

(defthm rationalp-of-rts-closure-error
  (implies (rationalp tangent)
           (rationalp (rts-closure-error n tangent)))
  :hints
  (("Goal"
    :use ((:instance qcx-rationalp-of-one)
          (:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil))
          (:instance qcx-rationalp-of-rct-advance
                     (steps n)
                     (current (qcx-one))
                     (seed (rct-rational-unit nil tangent)))
          (:instance rationalp-of-qcx-dist
                     (x (rct-advance
                         n (qcx-one)
                         (rct-rational-unit nil tangent)))
                     (y (qcx-one))))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(rts-closure-error)))))

(defthm rts-nfix-when-posp
  (implies (posp n)
           (equal (nfix n) n))
  :hints (("Goal" :in-theory (enable posp nfix))))

(defthm rts-generated-parameter-certificate-correct
  (implies
   (rts-generated-parameter-certificatep n epsilon tangent)
   (rct-parameter-certificatep
    n epsilon
    (rts-generated-separation
     n (rct-rational-unit nil tangent))
    nil tangent))
  :hints
  (("Goal"
    :use ((:instance qcx-rationalp-of-rct-rational-unit
                     (other-chart nil))
          (:instance qcx-norm-square-of-rct-rational-unit
                     (other-chart nil))
          (:instance rts-generated-separation-is-rational
                     (seed (rct-rational-unit nil tangent)))
          (:instance rts-generated-separation-is-positive
                     (seed (rct-rational-unit nil tangent)))
          (:instance rts-generated-separation-certifies-proper-orbit
                     (seed (rct-rational-unit nil tangent))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-generated-parameter-certificatep
       rct-parameter-certificatep
       rct-seed-certificatep
       rts-closure-error
       rts-nfix-when-posp)))))

(defthm rts-generated-twiddle-system-correct
  (implies
   (rts-generated-parameter-certificatep n epsilon tangent)
   (rct-twiddle-systemp
    n epsilon
    (rts-generated-separation
     n (rct-rational-unit nil tangent))
    (rct-rational-unit nil tangent)
    (rct-twiddle-table n nil tangent)))
  :hints
  (("Goal"
    :use ((:instance rts-generated-parameter-certificate-correct)
          (:instance rct-rational-parameter-builder-correct
                     (separation
                      (rts-generated-separation
                       n (rct-rational-unit nil tangent)))
                     (other-chart nil)))
    :in-theory nil)))
