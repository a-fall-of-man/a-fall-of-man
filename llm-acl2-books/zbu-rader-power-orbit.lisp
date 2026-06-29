; Semantic power representation of generated Rader index orbits.
(in-package "ACL2")
(include-book "zbf-rader-index-certificate")
(include-book "workshops/2022/gamboa-primitive-roots/order-constructions" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(defthm rgi-nfix-when-natp
  (implies (natp x) (equal (nfix x) x)))

(defthm rgi-natp-of-one-less-when-positive
  (implies (and (natp x) (not (zp x)))
           (natp (1- x))))

(defthm rgi-natp-of-one-plus
  (implies (natp x) (natp (1+ x))))

(defthm rgi-natp-of-zero
  (natp 0))

(defun rgi-power-orbit-aux (count exponent generator modulus)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (pfield::pow generator (nfix exponent) modulus)
          (rgi-power-orbit-aux
           (1- count) (1+ (nfix exponent)) generator modulus))))

(defthm len-of-rgi-power-orbit-aux
  (equal (len (rgi-power-orbit-aux count exponent generator modulus))
         (nfix count))
  :hints (("Goal" :in-theory (enable rgi-power-orbit-aux))))

(defthm rgi-mod-product-power-step
  (implies
   (and (integerp modulus)
        (< 1 modulus)
        (pfield::fep generator modulus)
        (natp exponent))
   (equal (mod (* (pfield::pow generator exponent modulus)
                  generator)
               modulus)
          (pfield::pow generator (1+ exponent) modulus)))
  :hints
  (("Goal"
    :use
    ((:instance pfield::pow-of-+
                (a generator) (b exponent) (c 1) (p modulus))
     (:instance pfield::pow-of-1-arg2
                (a generator) (p modulus)))
    :in-theory (enable pfield::mul))))

(defthm rgi-natp-of-positive-integer
  (implies (and (integerp x) (< 0 x))
           (natp x)))

(defthm rgi-natp-of-one-less-positive-integer
  (implies (and (integerp x) (< 1 x))
           (natp (1- x))))

(defthm rgi-nfix-of-fep
  (implies (pfield::fep x p)
           (equal (nfix x) x))
  :hints
  (("Goal"
    :use ((:instance rgi-nfix-when-natp))
    :in-theory (enable pfield::fep))))

(defthm rgi-mod-of-fep
  (implies
   (and (integerp p)
        (< 1 p)
        (pfield::fep x p))
   (equal (mod x p) x))
  :hints
  (("Goal"
    :use ((:instance mod-x-y-=-x (x x) (y p)))
    :in-theory (enable pfield::fep))))

(defthm rgi-power-orbit-aux-when-zp
  (implies (zp count)
           (equal (rgi-power-orbit-aux
                   count exponent generator modulus)
                  nil))
  :hints
  (("Goal"
    :expand ((rgi-power-orbit-aux count exponent generator modulus))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-power-orbit-aux-open
  (implies
   (not (zp count))
   (equal
    (rgi-power-orbit-aux count exponent generator modulus)
    (cons (pfield::pow generator (nfix exponent) modulus)
          (rgi-power-orbit-aux
           (1- count) (1+ (nfix exponent)) generator modulus))))
  :hints
  (("Goal"
    :expand ((rgi-power-orbit-aux count exponent generator modulus))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-orbit-aux-from-power-when-zp
  (implies
   (zp count)
   (equal
    (rgi-orbit-aux
     count (pfield::pow generator exponent modulus)
     generator modulus)
    nil))
  :hints
  (("Goal"
    :expand
    ((rgi-orbit-aux
      count (pfield::pow generator exponent modulus)
      generator modulus))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-orbit-aux-from-power-open
  (implies
   (and (not (zp count))
        (integerp modulus)
        (< 1 modulus)
        (pfield::fep generator modulus)
        (natp exponent))
   (equal
    (rgi-orbit-aux
     count (pfield::pow generator exponent modulus)
     generator modulus)
    (cons
     (pfield::pow generator exponent modulus)
     (rgi-orbit-aux
      (1- count)
      (pfield::pow generator (1+ exponent) modulus)
      generator modulus))))
  :hints
  (("Goal"
    :use ((:instance rgi-mod-product-power-step))
    :expand
    ((rgi-orbit-aux
      count (pfield::pow generator exponent modulus)
      generator modulus))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-nfix-when-natp
       rgi-natp-of-positive-integer
       rgi-nfix-of-fep
       rgi-mod-of-fep
       pfield::fep-of-pow
       pfield::natp-of-pow)))))

(defthm rgi-orbit-aux-from-power
  (implies
   (and (integerp modulus)
        (< 1 modulus)
        (pfield::fep generator modulus)
        (natp count)
        (natp exponent))
   (equal
    (rgi-orbit-aux
     count (pfield::pow generator exponent modulus)
     generator modulus)
    (rgi-power-orbit-aux count exponent generator modulus)))
  :hints
  (("Goal"
    :induct (rgi-power-orbit-aux count exponent generator modulus)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:induction rgi-power-orbit-aux)
       rgi-power-orbit-aux-when-zp
       rgi-power-orbit-aux-open
       rgi-orbit-aux-from-power-when-zp
       rgi-orbit-aux-from-power-open
       rgi-natp-of-one-less-when-positive
       rgi-natp-of-one-plus
       rgi-nfix-when-natp)))))

(defthm rgi-orbit-as-power-orbit
  (implies
   (and (integerp p)
        (< 1 p)
        (pfield::fep generator p))
   (equal (rgi-orbit p generator)
          (rgi-power-orbit-aux (1- p) 0 generator p)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-orbit-aux-from-power
                (modulus p)
                (count (1- p))
                (exponent 0)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '((:definition rgi-orbit)
       rgi-natp-of-positive-integer
       rgi-natp-of-one-less-positive-integer
       rgi-natp-of-zero
       rgi-nfix-when-natp
       pfield::pow-of-0-arg2)))))
