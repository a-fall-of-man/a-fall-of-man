; Totality of the finite primitive-root search for prime fields.
; This bridges the project search to the constructive primitive-root theorem
; already certified in the ACL2 community books.
(in-package "ACL2")

(include-book "zcr-primitive-root-certificate-search")
(include-book "workshops/2022/gamboa-primitive-roots/order-constructions" :dir :system)

(defthm zct-search-aux-complete-from-witness
  (implies
   (and (natp remaining)
        (natp candidate)
        (natp witness)
        (<= candidate witness)
        (< witness (+ candidate remaining))
        (zcr-primitive-root-candidatep witness p))
   (consp (zcr-primitive-root-search-aux remaining candidate p)))
  :hints
  (("Goal"
    :induct (zcr-primitive-root-search-aux remaining candidate p)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcr-primitive-root-search-aux
       zcr-primitive-root-candidatep
       nfix zp natp
       default-less-than-1 default-less-than-2
       default-plus-1 default-plus-2)))))

(defthm zct-prime-primitive-root-is-field-element
  (implies (dm::primep p)
           (pfield::fep (pfield::primitive-root p) p))
  :hints
  (("Goal"
    :use
    ((:instance pfield::fep-primitive-root-aux
                (k (1- p))
                (p p))
     (:instance primep-forward-to-posp
                (x p))
     (:instance primep-forward-to-bound
                (x p))
     (:instance dm::primep-gt-1
                (p p)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(pfield::primitive-root posp natp)))))

(defthm zct-prime-primitive-root-is-nonzero
  (implies (dm::primep p)
           (not (equal (pfield::primitive-root p) 0)))
  :hints
  (("Goal"
    :use
    ((:instance pfield::fep-primite-root-non-zero
                (k (1- p))
                (p p))
     (:instance primep-forward-to-posp
                (x p))
     (:instance primep-forward-to-bound
                (x p))
     (:instance dm::divides-self
                (x (1- p))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(pfield::primitive-root natp posp)))))

(defthm zct-prime-primitive-root-has-full-order
  (implies (dm::primep p)
           (equal (pfield::order (pfield::primitive-root p) p)
                  (1- p)))
  :hints
  (("Goal"
    :use ((:instance pfield::primes-have-primitive-roots
                (p p)))
    :in-theory (theory 'minimal-theory))))

(defthm zct-prime-primitive-root-is-candidate
  (implies (dm::primep p)
           (zcr-primitive-root-candidatep
            (pfield::primitive-root p) p))
  :hints
  (("Goal"
    :use
    ((:instance zct-prime-primitive-root-is-field-element)
     (:instance zct-prime-primitive-root-is-nonzero)
     (:instance zct-prime-primitive-root-has-full-order))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcr-primitive-root-candidatep)))))

(defthm zct-prime-primitive-root-is-natural
  (implies (dm::primep p)
           (natp (pfield::primitive-root p)))
  :hints
  (("Goal"
    :use ((:instance zct-prime-primitive-root-is-field-element))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(pfield::fep-fw-to-natp)))))


(defthm zct-prime-primitive-root-is-positive
  (implies (dm::primep p)
           (< 0 (pfield::primitive-root p)))
  :hints
  (("Goal"
    :use
    ((:instance zct-prime-primitive-root-is-natural)
     (:instance zct-prime-primitive-root-is-nonzero))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(natp)))))

(defthm zct-prime-primitive-root-is-less-than-p
  (implies (dm::primep p)
           (< (pfield::primitive-root p) p))
  :hints
  (("Goal"
    :use ((:instance zct-prime-primitive-root-is-field-element))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(pfield::fep-fw-to-bound)))))

(defthm zct-primitive-root-search-succeeds-for-primes
  (implies (dm::primep p)
           (zcr-generated-primitive-rootp p))
  :hints
  (("Goal"
    :use
    ((:instance zct-search-aux-complete-from-witness
                (remaining (nfix p))
                (candidate 1)
                (witness (pfield::primitive-root p)))
     (:instance zct-prime-primitive-root-is-candidate)
     (:instance zct-prime-primitive-root-is-natural)
     (:instance zct-prime-primitive-root-is-positive)
     (:instance zct-prime-primitive-root-is-less-than-p)
     (:instance primep-forward-to-bound
                (x p))
     (:instance dm::primep-gt-1
                (p p)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcr-primitive-root-search
       zcr-generated-primitive-rootp
       nfix natp posp)))))
