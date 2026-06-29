; Permutation and pointwise semantics of the generated inverse Rader orbit.
(in-package "ACL2")
(include-book "zbw-rader-orbit-permutation")
(include-book "kestrel/lists-light/reverse" :dir :system)
(include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)

(defthm rgi-positive-residuesp-of-append
  (equal (rgi-positive-residuesp p (append xs ys))
         (and (rgi-positive-residuesp p xs)
              (rgi-positive-residuesp p ys)))
  :hints (("Goal" :induct (rgi-positive-residuesp p xs)
           :in-theory (enable rgi-positive-residuesp))))

(defthm rgi-positive-residuesp-of-reverse
  (implies (rgi-positive-residuesp p xs)
           (rgi-positive-residuesp p (reverse xs)))
  :hints (("Goal" :induct (rgi-positive-residuesp p xs)
           :in-theory (enable reverse rgi-positive-residuesp))))

(defthm rgi-positive-residuesp-of-cdr
  (implies (rgi-positive-residuesp p xs)
           (rgi-positive-residuesp p (cdr xs)))
  :hints (("Goal" :in-theory (enable rgi-positive-residuesp))))

(defthm rgi-positive-residuesp-of-cons-one
  (implies
   (and (integerp p)
        (< 1 p)
        (rgi-positive-residuesp p xs))
   (rgi-positive-residuesp p (cons 1 xs)))
  :hints (("Goal" :in-theory (enable rgi-positive-residuesp))))

(defthm rgi-primep-implies-integer-greater-than-one
  (implies (dm::primep p)
           (and (integerp p)
                (< 1 p)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable dm::primep))))

(defthm car-of-rgi-orbit
  (implies
   (and (integerp p)
        (< 1 p)
        (pfield::fep generator p))
   (equal (car (rgi-orbit p generator)) 1))
  :hints
  (("Goal"
    :use ((:instance nth-of-rgi-orbit (index 0)))
    :in-theory (enable nth pfield::pow-of-0-arg2))))

(defthm consp-of-rgi-orbit-aux
  (implies (not (zp count))
           (consp (rgi-orbit-aux count value generator modulus)))
  :hints
  (("Goal"
    :expand ((rgi-orbit-aux count value generator modulus))
    :in-theory (theory 'minimal-theory))))

(defthm consp-of-rgi-orbit
  (implies
   (and (integerp p)
        (< 1 p))
   (consp (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance consp-of-rgi-orbit-aux
                (count (1- (nfix p)))
                (value 1)
                (modulus p)))
    :in-theory
    (enable rgi-orbit
            rgi-natp-of-positive-integer
            rgi-nfix-when-natp))))

(defthm len-of-cdr-of-rgi-orbit
  (implies
   (and (integerp p)
        (< 1 p))
   (equal (len (cdr (rgi-orbit p generator)))
          (- p 2)))
  :hints
  (("Goal"
    :use
    ((:instance len-of-rgi-orbit)
     (:instance consp-of-rgi-orbit))
    :in-theory
    (enable rgi-natp-of-positive-integer
            rgi-nfix-when-natp))))

(defthm len-of-rgi-inverse-orbit
  (implies
   (and (integerp p)
        (< 1 p))
   (equal (len (rgi-inverse-orbit p generator))
          (1- p)))
  :hints
  (("Goal"
    :use
    ((:instance consp-of-rgi-orbit)
     (:instance len-of-cdr-of-rgi-orbit))
    :in-theory
    (enable rgi-inverse-orbit))))

(defthm rgi-positive-residuesp-of-inverse-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0)))
   (rgi-positive-residuesp p (rgi-inverse-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-positive-residuesp-of-orbit)
     (:instance rgi-positive-residuesp-of-cdr
                (xs (rgi-orbit p generator)))
     (:instance rgi-positive-residuesp-of-reverse
                (xs (cdr (rgi-orbit p generator))))
     (:instance rgi-positive-residuesp-of-cons-one
                (xs (reverse (cdr (rgi-orbit p generator)))))
     (:instance consp-of-rgi-orbit))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition rgi-inverse-orbit)
       rgi-primep-implies-integer-greater-than-one)))))

(defthm no-duplicatesp-equal-of-rgi-inverse-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (no-duplicatesp-equal (rgi-inverse-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance no-duplicatesp-equal-of-rgi-orbit)
     (:instance car-of-rgi-orbit))
    :in-theory
    (enable rgi-inverse-orbit
            no-duplicatesp-equal
            dm::primep))))

(defthm rgi-permutationp-of-generated-inverse-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rgi-permutationp p (rgi-inverse-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance len-of-rgi-inverse-orbit)
     (:instance rgi-positive-residuesp-of-inverse-orbit)
     (:instance no-duplicatesp-equal-of-rgi-inverse-orbit))
    :in-theory
    (enable rgi-permutationp dm::primep))))
