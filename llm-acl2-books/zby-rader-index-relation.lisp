; Universal exponent relation for generated Rader input, kernel, and output indices.
(in-package "ACL2")
(include-book "zbx-rader-inverse-orbit")
(include-book "kestrel/lists-light/nth" :dir :system)

(defthm rgi-nth-of-cons-one-reverse-cdr
  (implies
   (and (consp xs)
        (natp a)
        (< 0 a)
        (< a (len xs)))
   (equal
    (nth a (cons 1 (reverse (cdr xs))))
    (nth (- (len xs) a) xs)))
  :hints
  (("Goal"
    :use
    ((:instance nth-of-reverse
                (n (1- a))
                (x (cdr xs))))
    :in-theory
    (enable nth-of-cdr))))

(defthm nth-zero-of-rgi-inverse-orbit
  (implies
   (and (integerp p)
        (< 1 p))
   (equal (nth 0 (rgi-inverse-orbit p generator)) 1))
  :hints
  (("Goal"
    :use ((:instance consp-of-rgi-orbit))
    :in-theory (enable rgi-inverse-orbit))))

(defthm nth-positive-of-rgi-inverse-orbit
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp a)
        (< 0 a)
        (< a (1- p)))
   (equal
    (nth a (rgi-inverse-orbit p generator))
    (pfield::pow generator (- (1- p) a) p)))
  :hints
  (("Goal"
    :use
    ((:instance consp-of-rgi-orbit)
     (:instance len-of-rgi-orbit)
     (:instance rgi-nth-of-cons-one-reverse-cdr
                (xs (rgi-orbit p generator)))
     (:instance nth-of-rgi-orbit
                (index (- (1- p) a))))
    :in-theory
    (enable rgi-inverse-orbit))))

(defthm rgi-zp-of-natp-nonpositive
  (implies (and (natp x) (<= x 0))
           (zp x)))

(defthm rgi-not-zp-when-positive
  (implies (and (natp x) (< 0 x))
           (not (zp x))))

(defthm rgi-natural-nonpositive-is-zero
  (implies (and (natp x) (<= x 0))
           (equal x 0))
  :rule-classes nil)

(defthm nth-of-rgi-inverse-orbit-piecewise
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp a)
        (< a (1- p)))
   (equal
    (nth a (rgi-inverse-orbit p generator))
    (if (zp a)
        1
      (pfield::pow generator (- (1- p) a) p))))
  :hints
  (("Goal"
    :cases ((zp a))
    :use
    ((:instance nth-zero-of-rgi-inverse-orbit)
     (:instance nth-positive-of-rgi-inverse-orbit)
     (:instance rgi-natural-nonpositive-is-zero (x a)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-zp-of-natp-nonpositive
       rgi-not-zp-when-positive)))))
