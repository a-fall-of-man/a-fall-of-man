; Universal permutation theorem for generated Rader power orbits.
(in-package "ACL2")
(include-book "zbv-rader-power-permutation")
(include-book "std/lists/index-of" :dir :system)

(defthm rgi-positive-residuesp-of-power-orbit-aux
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (natp count)
        (natp exponent))
   (rgi-positive-residuesp
    p (rgi-power-orbit-aux count exponent generator p)))
  :hints
  (("Goal"
    :induct (rgi-power-orbit-aux count exponent generator p)
    :in-theory
    (enable rgi-power-orbit-aux
            rgi-positive-residuesp))
   ("Subgoal *1/2"
    :use
    ((:instance pfield::pow-not-zero-for-non-zero-base
                (a generator) (n exponent) (p p))))))

(defthm rgi-positive-residuesp-of-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0)))
   (rgi-positive-residuesp p (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-orbit-as-power-orbit)
     (:instance rgi-positive-residuesp-of-power-orbit-aux
                (count (1- p))
                (exponent 0)))
    :in-theory
    (enable dm::primep))))

(defthm rgi-head-not-member-of-later-powers
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp exponent)
        (natp count)
        (< (+ exponent count) (1- p)))
   (not
    (member-equal
     (pfield::pow generator exponent p)
     (rgi-power-orbit-aux count (1+ exponent) generator p))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance nth-of-index-when-member
                (k (pfield::pow generator exponent p))
                (x (rgi-power-orbit-aux
                    count (1+ exponent) generator p)))
     (:instance index-of-<-len
                (k (pfield::pow generator exponent p))
                (x (rgi-power-orbit-aux
                    count (1+ exponent) generator p)))
     (:instance nth-of-rgi-power-orbit-aux
                (index
                 (index-of
                  (pfield::pow generator exponent p)
                  (rgi-power-orbit-aux
                   count (1+ exponent) generator p)))
                (exponent (1+ exponent))
                (modulus p))
     (:instance rgi-powers-distinct-before-full-order
                (i exponent)
                (j (+ 1 exponent
                      (index-of
                       (pfield::pow generator exponent p)
                       (rgi-power-orbit-aux
                        count (1+ exponent) generator p))))))
    :in-theory
    (enable len-of-rgi-power-orbit-aux))))

(defthm no-duplicatesp-equal-of-rgi-power-orbit-aux
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp exponent)
        (natp count)
        (<= (+ exponent count) (1- p)))
   (no-duplicatesp-equal
    (rgi-power-orbit-aux count exponent generator p)))
  :hints
  (("Goal"
    :induct (rgi-power-orbit-aux count exponent generator p)
    :in-theory
    (enable rgi-power-orbit-aux
            no-duplicatesp-equal))
   ("Subgoal *1/2"
    :use
    ((:instance rgi-head-not-member-of-later-powers
                (count (1- count)))))))

(defthm no-duplicatesp-equal-of-rgi-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (no-duplicatesp-equal (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-orbit-as-power-orbit)
     (:instance no-duplicatesp-equal-of-rgi-power-orbit-aux
                (count (1- p))
                (exponent 0)))
    :in-theory
    (enable dm::primep))))

(defthm rgi-permutationp-of-generated-orbit
  (implies
   (and (dm::primep p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rgi-permutationp p (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-positive-residuesp-of-orbit)
     (:instance no-duplicatesp-equal-of-rgi-orbit))
    :in-theory
    (enable rgi-permutationp
            len-of-rgi-orbit
            dm::primep))))
