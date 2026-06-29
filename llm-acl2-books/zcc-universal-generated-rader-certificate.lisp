; Universal certification of the complete generated Rader index system.
(in-package "ACL2")
(include-book "zcb-universal-rader-certificate")

(defthm rgi-relationp-aux-open
  (implies
   (not (zp count))
   (equal
    (rgi-relationp-aux count p inputs kernels outputs)
    (let ((a (1- (nfix count))))
      (and
       (rgi-relation-rowp (1- (nfix p)) a p
                          inputs kernels outputs)
       (rgi-relationp-aux (1- count) p
                          inputs kernels outputs)))))
  :hints
  (("Goal"
    :expand ((rgi-relationp-aux count p inputs kernels outputs))
    :in-theory nil)))

(defthm rgi-relationp-aux-zero
  (equal (rgi-relationp-aux 0 p inputs kernels outputs) t)
  :hints
  (("Goal"
    :expand ((rgi-relationp-aux 0 p inputs kernels outputs))
    :in-theory (enable zp))))

(defthm rgi-generated-relationp-aux-step
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp count)
        (not (zp count))
        (<= count (1- p))
        (rgi-relationp-aux
         (1- count) p
         (rgi-inverse-orbit p generator)
         (rgi-orbit p generator)
         (rgi-orbit p generator)))
   (rgi-relationp-aux
    count p
    (rgi-inverse-orbit p generator)
    (rgi-orbit p generator)
    (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-relationp-aux-open
                (inputs (rgi-inverse-orbit p generator))
                (kernels (rgi-orbit p generator))
                (outputs (rgi-orbit p generator)))
     (:instance rgi-generated-relation-rowp
                (a (1- count))
                (count (1- p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relationp-aux-open
       rgi-nfix-when-natp
       rgi-natp-of-positive-integer
       rgi-natp-of-one-less-positive-integer
       rgi-natp-of-predecessor
       rgi-predecessor-below-bound)))))

(defthm rgi-generated-relationp-aux
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp count)
        (<= count (1- p)))
   (rgi-relationp-aux
    count p
    (rgi-inverse-orbit p generator)
    (rgi-orbit p generator)
    (rgi-orbit p generator)))
  :hints
  (("Goal"
    :induct (rgi-count-induct count)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-count-induct)))
   ("Subgoal *1/2"
    :use ((:instance rgi-generated-relationp-aux-step))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-predecessor
       rgi-predecessor-not-above-bound)))
   ("Subgoal *1/1"
    :use
    ((:instance rgi-relationp-aux-zero
                (inputs (rgi-inverse-orbit p generator))
                (kernels (rgi-orbit p generator))
                (outputs (rgi-orbit p generator)))
     (:instance rgi-zp-natural-is-zero))
    :in-theory (theory 'minimal-theory))))

(defthm rgi-index-certificatep-of-generated-orbits
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rgi-index-certificatep
    p
    (rgi-inverse-orbit p generator)
    (rgi-orbit p generator)
    (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-permutationp-of-generated-inverse-orbit)
     (:instance rgi-permutationp-of-generated-orbit)
     (:instance rgi-generated-relationp-aux
                (count (1- p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-index-certificatep
       rgi-nfix-when-natp
       rgi-natp-of-positive-integer
       rgi-natp-of-one-less-positive-integer)))))

(defthm rgi-generated-index-certificatep-universal
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p)))
   (rgi-generated-index-certificatep p generator))
  :hints
  (("Goal"
    :use ((:instance rgi-index-certificatep-of-generated-orbits))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-generated-index-certificatep
       rgi-generated-inputs
       rgi-generated-kernels
       rgi-generated-outputs)))))
