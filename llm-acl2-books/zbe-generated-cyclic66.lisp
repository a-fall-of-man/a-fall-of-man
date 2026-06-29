; A generated rank-131 bilinear plan for length-66 cyclic convolution.
(in-package "ACL2")
(include-book "zbd-toom-cook-moment-certificate")
(local (include-book "zbt-universal-generated-compact"))

(defthm tc66-generated-compact-certificate
  (tc-generated-compact-certifiesp 66)
  :hints
  (("Goal"
    :use
    ((:instance tc-generated-compact-certifiesp-universal
                (n 66)))
    :in-theory (enable posp))))

(defthm tc66-generated-plan-certificate
  (tc-generated-plan-certifiesp 66)
  :hints (("Goal"
           :use ((:instance tc66-generated-compact-certificate)
                 (:instance
                  tc-generated-compact-certificate-implies-plan-certificate
                  (n 66)))
           :in-theory nil)))

(defthm tc66-generated-rank-is-131
  (equal (wbc-bank-rank (tc-plan-terms 66)) 131)
  :hints (("Goal"
           :use ((:instance tc-generated-rank (n 66)))
           :in-theory (disable tc-generated-rank))))

(defthm tc66-generated-cyclic-convolution-correct
  (implies (and (qcx-vectorp 66 xs)
                (qcx-vectorp 66 ys))
           (equal (tc-run 66 xs ys)
                  (wbc-cyclic-convolution 66 xs ys)))
  :hints (("Goal"
           :use ((:instance tc66-generated-compact-certificate)
                 (:instance
                  tc-compactly-certified-generated-plan-correct
                  (n 66)))
           :in-theory nil)))
