; Total witness-free rational WFTA generation for odd prime orders.
; The finite-field generator is found by certified bounded search.  The
; rational twiddle seed is explicit and needs neither sign search nor
; precision fuel.  Ordinary ACL2 only.
(in-package "ACL2")

(include-book "zct-primitive-root-search-totality")
(include-book "zcv-small-angle-orbit-separation")
(include-book "zcf-rader-index-implies-compact")

(defun zcw-total-generator (p)
  (zcr-generated-primitive-root p))

(defun zcw-total-tangent (p epsilon)
  (zcu-small-tangent p epsilon))

(defun zcw-total-seed (p epsilon)
  (zcu-small-seed p epsilon))

(defun zcw-total-separation (p epsilon)
  (rts-generated-separation p (zcw-total-seed p epsilon)))

(defun zcw-total-twiddle-table (p epsilon)
  (rct-twiddle-table p nil (zcw-total-tangent p epsilon)))

(defun zcw-total-wfta-object (p epsilon)
  (let ((generator (zcw-total-generator p)))
    (list
     p
     generator
     (zcw-total-tangent p epsilon)
     (zcw-total-separation p epsilon)
     (zcw-total-twiddle-table p epsilon)
     (rgi-generated-inputs p generator)
     (rgi-generated-kernels p generator)
     (rgi-generated-outputs p generator)
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p))))))

(defun zcw-total-wfta-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (rwd-rational-input-run
     p
     (rgi-generated-inputs p generator)
     (rgi-generated-kernels p generator)
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p)))
     xs
     (zcw-total-twiddle-table p epsilon))))

(defun zcw-total-direct-run (p epsilon xs)
  (let ((generator (zcw-total-generator p)))
    (rwd-direct-outputs
     (rwd-output-order (rgi-generated-outputs p generator))
     p
     (qcx-realify xs)
     (zcw-total-twiddle-table p epsilon))))

(defthm true-listp-of-zcw-total-wfta-object
  (true-listp (zcw-total-wfta-object p epsilon))
  :hints (("Goal" :in-theory (enable zcw-total-wfta-object))))

(defthm zcw-odd-prime-is-posp
  (implies (and (integerp p)
                (< 2 p))
           (posp p))
  :hints (("Goal" :in-theory (enable posp))))

(defthm zcw-total-generator-is-field-element
  (implies (dm::primep p)
           (pfield::fep (zcw-total-generator p) p))
  :hints
  (("Goal"
    :use ((:instance zct-primitive-root-search-succeeds-for-primes)
          (:instance zcr-generated-primitive-root-is-field-element))
    :in-theory (enable zcw-total-generator))))

(defthm zcw-total-generator-is-nonzero
  (implies (dm::primep p)
           (not (equal (zcw-total-generator p) 0)))
  :hints
  (("Goal"
    :use ((:instance zct-primitive-root-search-succeeds-for-primes)
          (:instance zcr-generated-primitive-root-is-nonzero))
    :in-theory (enable zcw-total-generator))))

(defthm zcw-total-generator-has-full-order
  (implies (dm::primep p)
           (equal (pfield::order (zcw-total-generator p) p)
                  (1- p)))
  :hints
  (("Goal"
    :use ((:instance zct-primitive-root-search-succeeds-for-primes)
          (:instance zcr-generated-primitive-root-has-full-order))
    :in-theory (enable zcw-total-generator))))

(defthm zcw-total-generated-compiler-certificate
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p))
   (rwd-compiled-certifiesp
    p
    (rgi-generated-inputs p (zcw-total-generator p))
    (rgi-generated-kernels p (zcw-total-generator p))
    (rgi-generated-outputs p (zcw-total-generator p))
    (tc-plan-terms (1- (nfix p)))
    (tc-plan-posts (1- (nfix p)))))
  :hints
  (("Goal"
    :use ((:instance zcw-total-generator-is-field-element)
          (:instance zcw-total-generator-is-nonzero)
          (:instance zcw-total-generator-has-full-order)
          (:instance zcf-generated-primitive-root-wfta-certificate
                     (generator (zcw-total-generator p))))
    :in-theory (theory 'minimal-theory))))

(defthm zcw-total-generated-twiddle-system
  (implies
   (and (< 2 p)
        (integerp p)
        (rationalp epsilon)
        (< 0 epsilon))
   (rct-twiddle-systemp
    p epsilon
    (zcw-total-separation p epsilon)
    (zcw-total-seed p epsilon)
    (zcw-total-twiddle-table p epsilon)))
  :hints
  (("Goal"
    :use ((:instance zcv-small-angle-twiddle-system-correct
                     (n p)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcw-total-separation
       zcw-total-seed
       zcw-total-tangent
       zcw-total-twiddle-table)))))

(defthm zcw-total-rational-wfta-correct
  (implies
   (and (dm::primep p)
        (integerp p)
        (< 2 p)
        (rationalp epsilon)
        (< 0 epsilon)
        (rational-listp xs)
        (equal (len xs) (nfix p)))
   (and
    (rwd-compiled-certifiesp
     p
     (rgi-generated-inputs p (zcw-total-generator p))
     (rgi-generated-kernels p (zcw-total-generator p))
     (rgi-generated-outputs p (zcw-total-generator p))
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p))))
    (rct-twiddle-systemp
     p epsilon
     (zcw-total-separation p epsilon)
     (zcw-total-seed p epsilon)
     (zcw-total-twiddle-table p epsilon))
    (equal (zcw-total-wfta-run p epsilon xs)
           (zcw-total-direct-run p epsilon xs))))
  :hints
  (("Goal"
    :use
    ((:instance zcw-odd-prime-is-posp)
     (:instance zcw-total-generator-is-field-element)
     (:instance zcw-total-generator-is-nonzero)
     (:instance zcw-total-generator-has-full-order)
     (:instance zcw-total-generated-compiler-certificate)
     (:instance zcw-total-generated-twiddle-system)
     (:instance zcu-small-tangent-rational
                (n p))
     (:instance rct-rwd-generated-table-correct
                (input-indices
                 (rgi-generated-inputs p (zcw-total-generator p)))
                (kernel-indices
                 (rgi-generated-kernels p (zcw-total-generator p)))
                (output-indices
                 (rgi-generated-outputs p (zcw-total-generator p)))
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))
                (other-chart nil)
                (tangent (zcw-total-tangent p epsilon))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(zcw-total-wfta-run
       zcw-total-direct-run
       zcw-total-twiddle-table
       zcw-total-tangent
       rwd-compile-outputs)))))
