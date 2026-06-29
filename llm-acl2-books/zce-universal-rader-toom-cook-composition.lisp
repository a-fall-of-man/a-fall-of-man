; Universal composition of compact Rader and generated Toom--Cook certificates.
(in-package "ACL2")

(include-book "zbk-rader-bank-certificate")
(include-book "zbt-universal-generated-compact")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lockstep composition of the two independent compact certificates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun urw-compact-join-induct (small-out outputs posts)
  (if (endp outputs)
      (list small-out outputs posts)
    (urw-compact-join-induct
     (1+ (nfix small-out)) (cdr outputs) (cdr posts))))

(defthm urw-tc-compact-bank-open
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

(defthm urw-not-zp-one-plus-len
  (not (zp (1+ (len xs)))))

(defthm urw-one-minus-one-plus-len
  (equal (1- (1+ (len xs))) (len xs)))

(defthm urw-tc-compact-bank-succ-len
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
    ((:instance urw-tc-compact-bank-open
                (count (1+ (len xs)))))
    :in-theory
    '(urw-not-zp-one-plus-len
      urw-one-minus-one-plus-len))))

(defthm urw-tc-compact-bank-zero
  (equal (tc-compact-bank-certifies-aux 0 out n posts)
         (endp posts))
  :hints
  (("Goal"
    :expand ((tc-compact-bank-certifies-aux 0 out n posts))
    :in-theory (enable zp nfix))))

(defthm urw-compact-certificates-join-aux
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
    :induct (urw-compact-join-induct small-out outputs posts)
    :expand
    ((tc-compact-bank-certifies-aux
      (len outputs) small-out (1- (nfix p)) posts)
     (rgi-compact-bankp-aux
      small-out p outputs inputs kernels)
     (rbk-compact-bankp
      small-out p outputs inputs kernels posts))
    :in-theory
    '(urw-compact-join-induct len car-cons cdr-cons
      urw-tc-compact-bank-open urw-tc-compact-bank-succ-len
      urw-tc-compact-bank-zero))))

(defthm urw-tc-generated-compact-open
  (equal
   (tc-generated-compact-certifiesp n)
   (tc-compact-bank-certifies-aux n 0 n (tc-plan-posts n)))
  :hints
  (("Goal"
    :expand ((tc-generated-compact-certifiesp n))
    :in-theory nil)))

(defthm urw-rgi-compact-bank-open
  (equal
   (rgi-compact-bankp p outputs inputs kernels)
   (and
    (equal (len outputs) (1- (nfix p)))
    (rgi-compact-bankp-aux 0 p outputs inputs kernels)))
  :hints
  (("Goal"
    :expand ((rgi-compact-bankp p outputs inputs kernels))
    :in-theory nil)))

(defthm urw-compact-certificates-join
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
    ((:instance urw-compact-certificates-join-aux
                (small-out 0)
                (posts (tc-plan-posts (1- (nfix p))))))
    :in-theory
    '(urw-tc-generated-compact-open
      urw-rgi-compact-bank-open))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A universal generated WFTA compiler theorem, parameterized only by the
;; finite Rader index and compact-output certificates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm urw-positive-implies-natural
  (implies (posp x) (natp x))
  :hints (("Goal" :in-theory (enable posp natp))))

(defthm urw-positive-residues-imply-natural-list
  (implies (rgi-positive-residuesp p xs)
           (rbk-nat-listp xs))
  :hints (("Goal"
           :induct (rgi-positive-residuesp p xs)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(rgi-positive-residuesp rbk-nat-listp
              urw-positive-implies-natural)))))

(defthm urw-index-certificate-implies-natural-outputs
  (implies (rgi-index-certificatep p inputs kernels outputs)
           (rbk-nat-listp outputs))
  :hints
  (("Goal"
    :use
    ((:instance rgi-index-certificate-implies-output-permutation)
     (:instance urw-positive-residues-imply-natural-list
                (xs outputs)))
    :in-theory '(rgi-permutationp))))

(defthm urw-generated-joint-compact-certificate
  (implies
   (and
    (posp (1- (nfix p)))
    (rgi-index-certificatep p inputs kernels outputs)
    (rgi-compact-bankp p outputs inputs kernels))
   (rbk-compact-bankp
    0 p outputs inputs kernels
    (tc-plan-posts (1- (nfix p)))))
  :hints
  (("Goal"
    :use
    ((:instance tc-generated-compact-certifiesp-universal
                (n (1- (nfix p))))
     (:instance urw-compact-certificates-join))
    :in-theory nil)))

(defthm urw-generated-bank-certificate
  (implies
   (and
    (posp p)
    (posp (1- (nfix p)))
    (rgi-index-certificatep p inputs kernels outputs)
    (rgi-compact-bankp p outputs inputs kernels))
   (rwd-bank-certifiesp
    p
    (rwd-output-order outputs)
    (rwd-full-terms
     p inputs kernels (tc-plan-terms (1- (nfix p))))
    (rwd-full-posts
     (len (tc-plan-terms (1- (nfix p))))
     (tc-plan-posts (1- (nfix p))))))
  :hints
  (("Goal"
    :use
    ((:instance urw-index-certificate-implies-natural-outputs)
     (:instance urw-generated-joint-compact-certificate)
     (:instance rbk-compact-bank-implies-full-certificate
                (posts (tc-plan-posts (1- (nfix p))))))
    :in-theory nil)))

(defthm urw-generated-wfta-certificate
  (implies
   (and
    (posp p)
    (posp (1- (nfix p)))
    (rgi-index-certificatep p inputs kernels outputs)
    (rgi-compact-bankp p outputs inputs kernels))
   (rwd-compiled-certifiesp
    p inputs kernels outputs
    (tc-plan-terms (1- (nfix p)))
    (tc-plan-posts (1- (nfix p)))))
  :hints
  (("Goal"
    :use
    ((:instance urw-generated-bank-certificate)
     (:instance rwd-compiled-certifiesp-is-bank-certifiesp
                (input-indices inputs)
                (kernel-indices kernels)
                (output-indices outputs)
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))))
    :in-theory
    '(rwd-compile-outputs
      rwd-compile-terms
      rwd-compile-posts))))

(defthm urw-generated-wfta-correct
  (implies
   (and
    (posp p)
    (posp (1- (nfix p)))
    (rgi-index-certificatep p inputs kernels outputs)
    (rgi-compact-bankp p outputs inputs kernels)
    (qcx-vectorp p xs)
    (qcx-vectorp p table))
   (equal
    (rwd-run
     p inputs kernels
     (tc-plan-terms (1- (nfix p)))
     (tc-plan-posts (1- (nfix p)))
     xs table)
    (rwd-direct-outputs (rwd-output-order outputs) p xs table)))
  :hints
  (("Goal"
    :use
    ((:instance urw-generated-wfta-certificate)
     (:instance rwd-compiled-transform-correct
                (input-indices inputs)
                (kernel-indices kernels)
                (output-indices outputs)
                (small-terms (tc-plan-terms (1- (nfix p))))
                (small-posts (tc-plan-posts (1- (nfix p))))))
    :in-theory '(rwd-compile-outputs))))

(defthm urw-generated-complex-product-count
  (equal
   (rwd-complex-product-count (tc-plan-terms n))
   (+ 2 (if (posp n) (1- (* 2 n)) 0)))
  :hints
  (("Goal"
    :use ((:instance len-of-tc-plan-terms))
    :in-theory '(rwd-complex-product-count))))
