; Universal pointwise relation for the generated Rader index lists.
(in-package "ACL2")
(include-book "zbz-rader-relation")
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)

(defthm rgi-natp-of-mod-positive
  (implies
   (and (integerp x)
        (posp n))
   (natp (mod x n))))

(defthm rgi-mod-less-than-positive
  (implies
   (and (rationalp x)
        (posp n))
   (< (mod x n) n)))

(defthm rgi-zero-index-product
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp m))
   (equal
    (mod (* 1 (pfield::pow generator m p)) p)
    (pfield::pow generator m p)))
  :hints
  (("Goal"
    :use ((:instance pfield::fep-of-pow
                     (x generator)
                     (n m)
                     (p p))
          (:instance pfield::mod-when-fep
                     (x (pfield::pow generator m p))
                     (p p)))
    :in-theory (enable pfield::fep))))

(defthm rgi-generated-relation-pointwise-zero
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp m)
        (< m (1- p)))
   (equal
    (nth (mod (- m 0) (1- p))
         (rgi-orbit p generator))
    (mod (* (nth 0 (rgi-inverse-orbit p generator))
            (nth m (rgi-orbit p generator)))
         p)))
  :hints
  (("Goal"
    :use
    ((:instance nth-zero-of-rgi-inverse-orbit)
     (:instance nth-of-rgi-orbit (index m))
     (:instance rgi-mod-below-positive (n (1- p)))
     (:instance rgi-zero-index-product))
    :in-theory (enable natp posp))))

(defthm rgi-generated-kernel-lookup
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp a)
        (natp m)
        (< a (1- p))
        (< m (1- p)))
   (equal
    (nth (mod (- m a) (1- p))
         (rgi-orbit p generator))
    (pfield::pow generator
                 (mod (- m a) (1- p))
                 p)))
  :hints
  (("Goal"
    :use
    ((:instance nth-of-rgi-orbit
                (index (mod (- m a) (1- p)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-mod-positive
       rgi-mod-less-than-positive
       natp posp)))))

(defthm rgi-generated-input-lookup-positive
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
    :use ((:instance nth-positive-of-rgi-inverse-orbit))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-generated-output-lookup
  (implies
   (and (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (natp m)
        (< m (1- p)))
   (equal
    (nth m (rgi-orbit p generator))
    (pfield::pow generator m p)))
  :hints
  (("Goal"
    :use ((:instance nth-of-rgi-orbit (index m)))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-generated-relation-pointwise-positive
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
    (nth (mod (- m a) (1- p))
         (rgi-orbit p generator))
    (mod (* (nth a (rgi-inverse-orbit p generator))
            (nth m (rgi-orbit p generator)))
         p)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-product-of-shifted-powers)
     (:instance rgi-generated-kernel-lookup)
     (:instance rgi-generated-input-lookup-positive)
     (:instance rgi-generated-output-lookup))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-generated-kernel-lookup
       rgi-generated-input-lookup-positive
       rgi-generated-output-lookup)))))

(defthm rgi-generated-relation-pointwise
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp a)
        (< a (1- p))
        (natp m)
        (< m (1- p)))
   (equal
    (nth (mod (- m a) (1- p))
         (rgi-orbit p generator))
    (mod (* (nth a (rgi-inverse-orbit p generator))
            (nth m (rgi-orbit p generator)))
         p)))
  :hints
  (("Goal"
    :cases ((zp a))
    :use
    ((:instance rgi-generated-relation-pointwise-zero)
     (:instance rgi-generated-relation-pointwise-positive)
     (:instance rgi-natural-nonpositive-is-zero (x a)))
    :in-theory (enable rgi-not-zp-when-positive natp))))
