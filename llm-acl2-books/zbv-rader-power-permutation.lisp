; Universal power-index semantics for generated Rader orbits.
(in-package "ACL2")
(include-book "zbu-rader-power-orbit")

(defthm rgi-zero-plus-natural
  (implies (natp x)
           (equal (+ 0 x) x)))

(defun rgi-power-orbit-nth-induct
  (count exponent index generator modulus)
  (declare (xargs :measure (nfix index)))
  (if (or (zp count) (zp index))
      (list count exponent index generator modulus)
    (rgi-power-orbit-nth-induct
     (1- count) (1+ (nfix exponent)) (1- index)
     generator modulus)))

(defthm nth-of-rgi-power-orbit-aux
  (implies
   (and (natp count)
        (natp exponent)
        (natp index)
        (< index count))
   (equal
    (nth index
         (rgi-power-orbit-aux count exponent generator modulus))
    (pfield::pow generator (+ exponent index) modulus)))
  :hints
  (("Goal"
    :induct (rgi-power-orbit-nth-induct
             count exponent index generator modulus)
    :in-theory
    (enable rgi-power-orbit-nth-induct
            rgi-power-orbit-aux))))

(defthm nth-of-rgi-orbit
  (implies
   (and (integerp p)
        (< 1 p)
        (pfield::fep generator p)
        (natp index)
        (< index (1- p)))
   (equal (nth index (rgi-orbit p generator))
          (pfield::pow generator index p)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-orbit-as-power-orbit)
     (:instance nth-of-rgi-power-orbit-aux
                (count (1- p))
                (exponent 0)
                (modulus p)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-one-less-positive-integer
       rgi-natp-of-zero
       rgi-zero-plus-natural)))))

(defthm rgi-posp-of-nonzero-fep
  (implies (and (pfield::fep x p)
                (not (equal x 0)))
           (posp x))
  :hints (("Goal" :in-theory (enable pfield::fep))))

(defthm rgi-powers-distinct-before-full-order
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp i)
        (natp j)
        (< i j)
        (< j (1- p)))
   (not (equal (pfield::pow generator i p)
               (pfield::pow generator j p))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance pfield::pow-of-+
                (a generator) (b i) (c 1) (p p))
     (:instance pfield::pow-of-+
                (a generator) (b j) (c 1) (p p))
     (:instance pfield::pow-of-1-arg2
                (a generator) (p p))
     (:instance pfield::equal-powers-means-some-power-is-1
                (x generator) (i (1+ i)) (j (1+ j)) (p p))
     (:instance pfield::pow-<-order
                (x generator) (n (- j i)) (p p))))))
