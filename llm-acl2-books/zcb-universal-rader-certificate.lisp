; Lift the universal generated Rader relation through its executable checkers.
(in-package "ACL2")
(include-book "zca-universal-rader-relation")

(defthm rgi-relation-rowp-open
  (implies
   (not (zp count))
   (equal
    (rgi-relation-rowp count a p inputs kernels outputs)
    (let* ((n (1- (nfix p)))
           (m (1- (nfix count))))
      (and
       (equal (nth (mod (- m (nfix a)) n) kernels)
              (mod (* (nth (nfix a) inputs)
                      (nth m outputs))
                   (nfix p)))
       (rgi-relation-rowp (1- count) a p
                          inputs kernels outputs)))))
  :hints
  (("Goal"
    :expand ((rgi-relation-rowp count a p inputs kernels outputs))
    :in-theory nil)))

(defthm rgi-relation-rowp-zero
  (equal (rgi-relation-rowp 0 a p inputs kernels outputs) t)
  :hints
  (("Goal"
    :expand ((rgi-relation-rowp 0 a p inputs kernels outputs))
    :in-theory (enable zp))))

(defthm rgi-natp-of-predecessor
  (implies
   (and (natp count)
        (not (zp count)))
   (natp (1- count))))

(defthm rgi-predecessor-below-bound
  (implies
   (and (natp count)
        (not (zp count))
        (integerp n)
        (<= count n))
   (< (1- count) n)))

(defthm rgi-predecessor-not-above-bound
  (implies
   (and (natp count)
        (not (zp count))
        (integerp n)
        (<= count n))
   (<= (1- count) n)))



(defthm rgi-zp-natural-is-zero
  (implies
   (and (natp count)
        (zp count))
   (equal count 0))
  :rule-classes nil)

(defun rgi-count-induct (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (rgi-count-induct (1- count))))

(defthm rgi-generated-relation-rowp-step
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp a)
        (< a (1- p))
        (natp count)
        (not (zp count))
        (<= count (1- p))
        (rgi-relation-rowp
         (1- count) a p
         (rgi-inverse-orbit p generator)
         (rgi-orbit p generator)
         (rgi-orbit p generator)))
   (rgi-relation-rowp
    count a p
    (rgi-inverse-orbit p generator)
    (rgi-orbit p generator)
    (rgi-orbit p generator)))
  :hints
  (("Goal"
    :use
    ((:instance rgi-relation-rowp-open
                (inputs (rgi-inverse-orbit p generator))
                (kernels (rgi-orbit p generator))
                (outputs (rgi-orbit p generator)))
     (:instance rgi-generated-relation-pointwise
                (m (1- count))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-relation-rowp-open
       rgi-nfix-when-natp
       rgi-natp-of-positive-integer
       rgi-natp-of-predecessor
       rgi-predecessor-below-bound)))))

(defthm rgi-generated-relation-rowp
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (pfield::fep generator p)
        (not (equal generator 0))
        (equal (pfield::order generator p) (1- p))
        (natp a)
        (< a (1- p))
        (natp count)
        (<= count (1- p)))
   (rgi-relation-rowp
    count a p
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
    :use ((:instance rgi-generated-relation-rowp-step))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rgi-natp-of-predecessor
       rgi-predecessor-not-above-bound)))
   ("Subgoal *1/1"
    :use
    ((:instance rgi-relation-rowp-zero
                (inputs (rgi-inverse-orbit p generator))
                (kernels (rgi-orbit p generator))
                (outputs (rgi-orbit p generator)))
     (:instance rgi-zp-natural-is-zero))
    :in-theory (theory 'minimal-theory))))

