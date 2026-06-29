; A generated rank-133 Rader/Winograd transform of prime length 67.
(in-package "ACL2")
(include-book "zbk-rader-bank-certificate")
(include-book "zcc-universal-generated-rader-certificate")
(include-book "workshops/2022/gamboa-primitive-roots/order-constructions" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Independent compact certificates compose in lockstep.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun gr67-compact-join-induct (small-out outputs posts)
  (if (endp outputs)
      (list small-out outputs posts)
    (gr67-compact-join-induct
     (1+ (nfix small-out)) (cdr outputs) (cdr posts))))

(defthm gr67-tc-compact-bank-open
  (implies
   (not (zp count))
   (equal
    (tc-compact-bank-certifies-aux count out n posts)
    (and
     (consp posts)
     (tc-compact-post-certifiesp n (nfix out) (car posts))
     (tc-compact-bank-certifies-aux
      (1- count) (1+ (nfix out)) n (cdr posts)))))
  :hints
  (("Goal"
    :expand ((tc-compact-bank-certifies-aux count out n posts))
    :in-theory nil)))

(defthm gr67-not-zp-one-plus-len
  (not (zp (1+ (len xs)))))

(defthm gr67-one-minus-one-plus-len
  (equal (1- (1+ (len xs))) (len xs)))

(defthm gr67-tc-compact-bank-succ-len
  (equal
   (tc-compact-bank-certifies-aux (1+ (len xs)) out n posts)
   (and
    (consp posts)
    (tc-compact-post-certifiesp n (nfix out) (car posts))
    (tc-compact-bank-certifies-aux
     (len xs) (1+ (nfix out)) n (cdr posts))))
  :hints
  (("Goal"
    :use
    ((:instance gr67-tc-compact-bank-open
                (count (1+ (len xs)))))
    :in-theory
    '(gr67-not-zp-one-plus-len
      gr67-one-minus-one-plus-len))))

(defthm gr67-tc-compact-bank-zero
  (equal (tc-compact-bank-certifies-aux 0 out n posts)
         (endp posts))
  :hints
  (("Goal"
    :expand ((tc-compact-bank-certifies-aux 0 out n posts))
    :in-theory (enable zp nfix))))

(defthm gr67-compact-certificates-join-aux
  (implies
   (and
    (tc-compact-bank-certifies-aux
     (len outputs) small-out (1- (nfix p)) posts)
    (rgi-compact-bankp-aux
     small-out p outputs inputs kernels))
   (rbk-compact-bankp
    small-out p outputs inputs kernels posts))
  :hints
  (("Goal"
    :induct (gr67-compact-join-induct small-out outputs posts)
    :expand
    ((tc-compact-bank-certifies-aux
      (len outputs) small-out (1- (nfix p)) posts)
     (rgi-compact-bankp-aux
      small-out p outputs inputs kernels)
     (rbk-compact-bankp
      small-out p outputs inputs kernels posts))
    :in-theory
    '(gr67-compact-join-induct len car-cons cdr-cons
      gr67-tc-compact-bank-open gr67-tc-compact-bank-succ-len
      gr67-tc-compact-bank-zero))))

(defthm gr67-tc-generated-compact-open
  (equal
   (tc-generated-compact-certifiesp n)
   (tc-compact-bank-certifies-aux n 0 n (tc-plan-posts n)))
  :hints
  (("Goal"
    :expand ((tc-generated-compact-certifiesp n))
    :in-theory nil)))

(defthm gr67-rgi-compact-bank-open
  (equal
   (rgi-compact-bankp p outputs inputs kernels)
   (and
    (equal (len outputs) (1- (nfix p)))
    (rgi-compact-bankp-aux 0 p outputs inputs kernels)))
  :hints
  (("Goal"
    :expand ((rgi-compact-bankp p outputs inputs kernels))
    :in-theory nil)))

(defthm gr67-compact-certificates-join
  (implies
   (and
    (tc-generated-compact-certifiesp (1- (nfix p)))
    (rgi-compact-bankp p outputs inputs kernels))
   (rbk-compact-bankp
    0 p outputs inputs kernels
    (tc-plan-posts (1- (nfix p)))))
  :hints
  (("Goal"
    :use
    ((:instance gr67-compact-certificates-join-aux
                (small-out 0)
                (posts (tc-plan-posts (1- (nfix p))))))
    :in-theory
    '(gr67-tc-generated-compact-open
      gr67-rgi-compact-bank-open))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The generated length-67 witness.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun gr67-generator ()
  (pfield::primitive-root 67))

(defun gr67-input-indices ()
  (rgi-generated-inputs 67 (gr67-generator)))

(defun gr67-kernel-indices ()
  (rgi-generated-kernels 67 (gr67-generator)))

(defun gr67-output-indices ()
  (rgi-generated-outputs 67 (gr67-generator)))

(defun gr67-small-terms ()
  (tc-plan-terms 66))

(defun gr67-small-posts ()
  (tc-plan-posts 66))

(defthm gr67-convolution-length
  (equal (1- (nfix 67)) 66))

(defthm gr67-small-terms-open
  (equal (gr67-small-terms) (tc-plan-terms 66))
  :hints (("Goal" :in-theory '(gr67-small-terms))))

(defthm gr67-small-posts-open
  (equal (gr67-small-posts) (tc-plan-posts 66))
  :hints (("Goal" :in-theory '(gr67-small-posts))))

(defthm gr67-prime
  (dm::primep 67)
  :hints (("Goal" :in-theory (enable dm::primep dm::least-divisor))))

(defthm gr67-generator-has-order-66
  (equal (pfield::order (gr67-generator) 67) 66)
  :hints
  (("Goal"
    :use ((:instance pfield::primes-have-primitive-roots (p 67))
          (:instance gr67-prime))
    :in-theory (enable gr67-generator))))

(defthm gr67-generator-fep
  (pfield::fep (gr67-generator) 67)
  :hints
  (("Goal"
    :use
    ((:instance pfield::fep-primitive-root-aux
                (k 66)
                (p 67)))
    :in-theory
    (enable gr67-generator
            pfield::primitive-root))))

(defthm gr67-generator-nonzero
  (not (equal (gr67-generator) 0))
  :hints
  (("Goal"
    :use
    ((:instance pfield::fep-primite-root-non-zero
                (k 66)
                (p 67))
     (:instance gr67-prime))
    :in-theory
    (enable gr67-generator
            pfield::primitive-root
            dm::divides))))

(defthm gr67-generated-index-certificate
  (rgi-index-certificatep
   67
   (gr67-input-indices)
   (gr67-kernel-indices)
   (gr67-output-indices))
  :hints
  (("Goal"
    :use
    ((:instance rgi-generated-index-certificatep-universal
                (p 67)
                (generator (gr67-generator)))
     (:instance gr67-prime)
     (:instance gr67-generator-fep)
     (:instance gr67-generator-nonzero)
     (:instance gr67-generator-has-order-66))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(gr67-input-indices
       gr67-kernel-indices
       gr67-output-indices
       rgi-generated-index-certificatep
       rgi-generated-inputs
       rgi-generated-kernels
       rgi-generated-outputs)))))

(defthm gr67-generated-rader-compact-certificate
  (rgi-compact-bankp
   67
   (gr67-output-indices)
   (gr67-input-indices)
   (gr67-kernel-indices))
  :hints
  (("Goal"
    :in-theory
    (enable gr67-input-indices
            gr67-kernel-indices
            gr67-output-indices
            gr67-generator
            pfield::primitive-root))))

(defthm gr67-nonzero-output-permutation
  (rgi-permutationp 67 (gr67-output-indices))
  :hints
  (("Goal"
    :use
    ((:instance gr67-generated-index-certificate)
     (:instance rgi-index-certificate-implies-output-permutation
                (p 67)
                (inputs (gr67-input-indices))
                (kernels (gr67-kernel-indices))
                (outputs (gr67-output-indices))))
    :in-theory nil)))

(defthm gr67-output-indices-natural
  (rbk-nat-listp (gr67-output-indices))
  :hints
  (("Goal"
    :in-theory
    (enable gr67-output-indices
            gr67-generator
            pfield::primitive-root))))

(defthm gr67-joint-compact-certificate
  (rbk-compact-bankp
   0 67
   (gr67-output-indices)
   (gr67-input-indices)
   (gr67-kernel-indices)
   (gr67-small-posts))
  :hints
  (("Goal"
    :use
    ((:instance tc66-generated-compact-certificate)
     (:instance gr67-generated-rader-compact-certificate)
     (:instance gr67-compact-certificates-join
                (p 67)
                (outputs (gr67-output-indices))
                (inputs (gr67-input-indices))
                (kernels (gr67-kernel-indices))))
    :in-theory
    '(gr67-convolution-length
      gr67-small-posts-open))))

(defthm gr67-positive-lengths
  (and (posp 67) (posp 66)))

(defthm gr67-generated-bank-certificate
  (rwd-bank-certifiesp
   67
   (rwd-output-order (gr67-output-indices))
   (rwd-full-terms
    67 (gr67-input-indices) (gr67-kernel-indices)
    (tc-plan-terms 66))
   (rwd-full-posts
    (len (tc-plan-terms 66)) (tc-plan-posts 66)))
  :hints
  (("Goal"
    :use
    ((:instance gr67-positive-lengths)
     (:instance gr67-joint-compact-certificate)
     (:instance gr67-output-indices-natural)
     (:instance rbk-compact-bank-implies-full-certificate
                (p 67)
                (outputs (gr67-output-indices))
                (inputs (gr67-input-indices))
                (kernels (gr67-kernel-indices))
                (posts (tc-plan-posts 66))))
    :in-theory
    '(gr67-convolution-length
      gr67-small-posts-open))))

(defthm gr67-generated-wfta-certificate
  (rwd-compiled-certifiesp
   67
   (gr67-input-indices)
   (gr67-kernel-indices)
   (gr67-output-indices)
   (gr67-small-terms)
   (gr67-small-posts))
  :hints
  (("Goal"
    :use
    ((:instance gr67-generated-bank-certificate)
     (:instance rwd-compiled-certifiesp-is-bank-certifiesp
                (p 67)
                (input-indices (gr67-input-indices))
                (kernel-indices (gr67-kernel-indices))
                (output-indices (gr67-output-indices))
                (small-terms (gr67-small-terms))
                (small-posts (gr67-small-posts))))
    :in-theory
    '(rwd-compile-outputs
      rwd-compile-terms
      rwd-compile-posts
      gr67-small-terms-open
      gr67-small-posts-open))))

(defthm gr67-complex-product-count-is-133
  (equal (rwd-complex-product-count (gr67-small-terms)) 133)
  :hints
  (("Goal"
    :use ((:instance tc66-generated-rank-is-131))
    :in-theory
    (enable rwd-complex-product-count
            wbc-bank-rank
            gr67-small-terms))))

(defthm gr67-generated-wfta-is-compiled-dft
  (implies
   (and (qcx-vectorp 67 xs)
        (qcx-vectorp 67 table))
   (equal
    (rwd-run
     67
     (gr67-input-indices)
     (gr67-kernel-indices)
     (gr67-small-terms)
     (gr67-small-posts)
     xs table)
    (rwd-direct-outputs
     (rwd-compile-outputs (gr67-output-indices))
     67 xs table)))
  :hints
  (("Goal"
    :use
    ((:instance gr67-generated-wfta-certificate)
     (:instance rwd-compiled-transform-correct
                (p 67)
                (input-indices (gr67-input-indices))
                (kernel-indices (gr67-kernel-indices))
                (output-indices (gr67-output-indices))
                (small-terms (gr67-small-terms))
                (small-posts (gr67-small-posts))))
    :in-theory nil)))

(defthm gr67-compiled-output-order
  (equal (rwd-compile-outputs (gr67-output-indices))
         (rwd-output-order (gr67-output-indices)))
  :hints (("Goal" :in-theory '(rwd-compile-outputs))))

(defthm gr67-generated-wfta-is-length-67-dft
  (implies
   (and (qcx-vectorp 67 xs)
        (qcx-vectorp 67 table))
   (equal
    (rwd-run
     67
     (gr67-input-indices)
     (gr67-kernel-indices)
     (gr67-small-terms)
     (gr67-small-posts)
     xs table)
    (rwd-direct-outputs
     (rwd-output-order (gr67-output-indices))
     67 xs table)))
  :hints
  (("Goal"
    :use ((:instance gr67-generated-wfta-is-compiled-dft))
    :in-theory '(gr67-compiled-output-order))))
