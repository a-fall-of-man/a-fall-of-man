; End-to-end rational WFTA generation from a finite stereographic
; sign-bisection certificate.  Ordinary ACL2 and exact rational arithmetic.
(in-package "ACL2")

(include-book "zcm-bisected-stereographic-twiddle")
(include-book "zcf-rader-index-implies-compact")

(defthm zcn-positive-integer-greater-than-two-is-posp
  (implies (and (integerp p)
                (< 2 p))
           (posp p))
  :hints (("Goal" :in-theory '(posp))))

(defthm zcn-bisected-generated-twiddle-system
  (implies
   (rts-bisected-twiddle-certificatep
    p epsilon precision lo hi radius)
   (rct-twiddle-systemp
    p epsilon
    (rts-generated-separation
     p (rct-rational-unit
        nil (rts-bisected-tangent precision p lo hi)))
    (rct-rational-unit
     nil (rts-bisected-tangent precision p lo hi))
    (rct-twiddle-table
     p nil (rts-bisected-tangent precision p lo hi))))
  :hints
  (("Goal"
    :use ((:instance rts-bisected-certificate-builds-twiddle-system
                     (n p)))
    :in-theory (theory 'minimal-theory))))

(defthm zcn-bisected-generated-primitive-root-wfta-correct
  (implies
   (and
    (dm::primep p)
    (integerp p)
    (< 2 p)
    (pfield::fep generator p)
    (not (equal generator 0))
    (equal (pfield::order generator p) (1- p))
    (rts-bisected-twiddle-certificatep
     p epsilon precision lo hi radius)
    (rational-listp xs)
    (equal (len xs) (nfix p)))
   (and
    (rct-twiddle-systemp
     p epsilon
     (rts-generated-separation
      p (rct-rational-unit
         nil (rts-bisected-tangent precision p lo hi)))
     (rct-rational-unit
      nil (rts-bisected-tangent precision p lo hi))
     (rct-twiddle-table
      p nil (rts-bisected-tangent precision p lo hi)))
    (equal
     (rwd-rational-input-run
      p
      (rgi-generated-inputs p generator)
      (rgi-generated-kernels p generator)
      (tc-plan-terms (1- (nfix p)))
      (tc-plan-posts (1- (nfix p)))
      xs
      (rct-twiddle-table
       p nil (rts-bisected-tangent precision p lo hi)))
     (rwd-direct-outputs
      (rwd-output-order (rgi-generated-outputs p generator))
      p
      (qcx-realify xs)
      (rct-twiddle-table
       p nil (rts-bisected-tangent precision p lo hi))))))
  :hints
  (("Goal"
    :use
    ((:instance zcn-positive-integer-greater-than-two-is-posp)
     (:instance zcn-bisected-generated-twiddle-system)
     (:instance rationalp-of-rts-bisected-tangent
                (n p))
     (:instance zcf-generated-primitive-root-wfta-certificate)
     (:instance rct-rwd-generated-table-correct
                (input-indices (rgi-generated-inputs p generator))
                (kernel-indices (rgi-generated-kernels p generator))
                (output-indices (rgi-generated-outputs p generator))
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))
                (other-chart nil)
                (tangent (rts-bisected-tangent
                          precision p lo hi))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(rts-bisected-twiddle-certificatep
       rwd-compile-outputs)))))
