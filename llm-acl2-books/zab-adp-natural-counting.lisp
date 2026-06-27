; zab-adp-natural-counting.lisp
;
; An executable natural-number instance of the algebraic DP kernel.

(in-package "ACL2")

(include-book "zaa-algebraic-dynamic-programming")

(defun nadp-valuep (x) (natp x))
(defun nadp-zero () 0)
(defun nadp-one () 1)
(defun nadp-plus (x y) (+ (nfix x) (nfix y)))
(defun nadp-times (x y) (* (nfix x) (nfix y)))

(verify-guards nadp-valuep)
(verify-guards nadp-zero)
(verify-guards nadp-one)
(verify-guards nadp-plus)
(verify-guards nadp-times)

(defthm nadp-semiring-laws
  (and (nadp-valuep (nadp-zero))
       (nadp-valuep (nadp-one))
       (implies (and (nadp-valuep x) (nadp-valuep y))
                (and (nadp-valuep (nadp-plus x y))
                     (nadp-valuep (nadp-times x y))))
       (implies (and (nadp-valuep x)
                     (nadp-valuep y)
                     (nadp-valuep z))
                (and (equal (nadp-plus (nadp-plus x y) z)
                            (nadp-plus x (nadp-plus y z)))
                     (equal (nadp-times (nadp-times x y) z)
                            (nadp-times x (nadp-times y z)))
                     (equal (nadp-times x (nadp-plus y z))
                            (nadp-plus (nadp-times x y)
                                       (nadp-times x z)))
                     (equal (nadp-times (nadp-plus x y) z)
                            (nadp-plus (nadp-times x z)
                                       (nadp-times y z))))))
  :hints (("Goal" :in-theory (enable nadp-valuep nadp-zero nadp-one
                                      nadp-plus nadp-times))))

(defthm nadp-semiring-commutative-identities-and-zero
  (implies (and (nadp-valuep x) (nadp-valuep y))
           (and (equal (nadp-plus x y) (nadp-plus y x))
                (equal (nadp-times x y) (nadp-times y x))
                (equal (nadp-plus (nadp-zero) x) x)
                (equal (nadp-plus x (nadp-zero)) x)
                (equal (nadp-times (nadp-one) x) x)
                (equal (nadp-times x (nadp-one)) x)
                (equal (nadp-times (nadp-zero) x) (nadp-zero))
                (equal (nadp-times x (nadp-zero)) (nadp-zero))))
  :hints (("Goal" :in-theory (enable nadp-valuep nadp-zero nadp-one
                                      nadp-plus nadp-times))))

(defattach (adp-valuep nadp-valuep)
           (adp-zero nadp-zero)
           (adp-one nadp-one)
           (adp-plus nadp-plus)
           (adp-times nadp-times))

(defconst *nadp-diamond*
  '((1)
    (0 (1 0))
    (0 (1 0) (1 1))
    (0 (1 1) (1 2))))

(assert-event (adp-program-validp *nadp-diamond*))
(assert-event (equal (adp-fast-value 3 *nadp-diamond*) 3))
