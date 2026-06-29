; Multiplicative exponent relation underlying universal Rader indexing.
(in-package "ACL2")
(include-book "zby-rader-index-relation")
(include-book "workshops/2022/gamboa-primitive-roots/order" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(defthm rgi-mod-below-positive
  (implies (and (natp x)
                (posp n)
                (< x n))
           (equal (mod x n) x))
  :hints
  (("Goal"
    :use ((:instance mod-when-< (x x) (y n)))
    :in-theory (enable natp))))

(defthm rgi-natp-of-shifted-exponent
  (implies (and (integerp p)
                (natp a)
                (< a (1- p)))
           (natp (- (1- p) a))))

(defthm rgi-natp-of-shifted-exponent-sum
  (implies (and (integerp p)
                (natp a)
                (< a (1- p))
                (natp m))
           (natp (+ (- (1- p) a) m))))

(defthm rgi-shifted-exponent-sum
  (equal (+ (- (1- p) a) m)
         (+ (1- p) (- m a))))

(defthm rgi-one-less-p-nonzero
  (implies (and (integerp p) (< 2 p))
           (not (equal (1- p) 0))))

(defthm rgi-mod-of-shifted-exponent-sum
  (implies (and (integerp p)
                (< 2 p)
                (integerp a)
                (integerp m))
           (equal (mod (+ (- (1- p) a) m) (1- p))
                  (mod (- m a) (1- p))))
  :hints
  (("Goal"
    :use ((:instance mod-of-+-same-arg1
                     (x (- m a))
                     (y (1- p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-shifted-exponent-sum
       rgi-one-less-p-nonzero)))))

(defthm rgi-pfield-mul-is-mod-product-of-powers
  (implies (and (integerp p)
                (< 2 p)
                (natp left)
                (natp right))
           (equal
            (pfield::mul (pfield::pow generator left p)
                         (pfield::pow generator right p)
                         p)
            (mod (* (pfield::pow generator left p)
                    (pfield::pow generator right p))
                 p)))
  :hints
  (("Goal"
    :use ((:instance pfield::natp-of-pow
                     (pfield::x generator) (pfield::n left) (pfield::p p))
          (:instance pfield::natp-of-pow
                     (pfield::x generator) (pfield::n right) (pfield::p p)))
    :in-theory (enable pfield::mul pos-fix ifix))))

(defthm rgi-integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defthm rgi-product-of-shifted-powers
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp a)
        (< 0 a)
        (< a (1- p))
        (natp m)
        (< m (1- p)))
   (equal
    (mod (* (pfield::pow generator (- (1- p) a) p)
            (pfield::pow generator m p))
         p)
    (pfield::pow generator (mod (- m a) (1- p)) p)))
  :hints
  (("Goal"
    :use
    ((:instance pfield::pow-of-+
                (pfield::a generator)
                (pfield::b (- (1- p) a))
                (pfield::c m)
                (pfield::p p))
     (:instance pfield::pow-mod-order
                (pfield::x generator)
                (pfield::n (+ (- (1- p) a) m))
                (pfield::p p))
     (:instance rgi-pfield-mul-is-mod-product-of-powers
                (left (- (1- p) a))
                (right m)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-shifted-exponent
       rgi-natp-of-shifted-exponent-sum
       rgi-integerp-when-natp
       rgi-mod-of-shifted-exponent-sum)))))
