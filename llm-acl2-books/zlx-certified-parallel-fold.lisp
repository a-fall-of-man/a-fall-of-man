; zlx-certified-parallel-fold.lisp
; Carrier-aware monoid folds, arbitrary reduction trees, block parallelism,
; and concrete theorems transported by DEF-FUNCTIONAL-INSTANCE.

(in-package "ACL2")

(include-book "tools/def-functional-instance" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zlx-certified-parallel-fold
  :parents (acl2::top)
  :short "Carrier-aware certified parallel decomposition of monoid folds.")

(encapsulate
  (((vpf-carrierp *) => *)
   ((vpf-op * *) => *)
   ((vpf-id) => *))
  (local (defun vpf-carrierp (x) (booleanp x)))
  (local (defun vpf-op (x y) (if x t (if y t nil))))
  (local (defun vpf-id () nil))
  (defthm vpf-carrierp-of-id (vpf-carrierp (vpf-id)))
  (defthm vpf-carrierp-of-op
    (implies (and (vpf-carrierp x) (vpf-carrierp y))
             (vpf-carrierp (vpf-op x y))))
  (defthm vpf-op-associative
    (implies (and (vpf-carrierp x) (vpf-carrierp y) (vpf-carrierp z))
             (equal (vpf-op (vpf-op x y) z)
                    (vpf-op x (vpf-op y z)))))
  (defthm vpf-op-left-identity
    (implies (vpf-carrierp x)
             (equal (vpf-op (vpf-id) x) x)))
  (defthm vpf-op-right-identity
    (implies (vpf-carrierp x)
             (equal (vpf-op x (vpf-id)) x))))

(defun vpf-all-carrierp (xs)
  (if (endp xs) t
    (and (vpf-carrierp (car xs))
         (vpf-all-carrierp (cdr xs)))))

(defun vpf-fold (xs)
  (if (endp xs) (vpf-id)
    (vpf-op (car xs) (vpf-fold (cdr xs)))))

(defthm vpf-carrierp-of-fold
  (implies (vpf-all-carrierp xs)
           (vpf-carrierp (vpf-fold xs)))
  :hints (("Goal" :induct (vpf-fold xs) :in-theory (enable vpf-all-carrierp vpf-fold))))

(defthm vpf-all-carrierp-of-append
  (equal (vpf-all-carrierp (append xs ys))
         (and (vpf-all-carrierp xs) (vpf-all-carrierp ys)))
  :hints (("Goal" :induct (len xs) :in-theory (enable vpf-all-carrierp))))

(defthm vpf-fold-of-nil
  (equal (vpf-fold nil) (vpf-id))
  :hints (("Goal" :in-theory (enable vpf-fold))))

(defthm vpf-fold-of-singleton
  (implies (vpf-carrierp x)
           (equal (vpf-fold (list x)) x))
  :hints (("Goal"
           :use ((:instance vpf-op-right-identity))
           :in-theory (enable vpf-fold))))

(defthm vpf-fold-of-append
  (implies (and (vpf-all-carrierp xs) (vpf-all-carrierp ys))
           (equal (vpf-fold (append xs ys))
                  (vpf-op (vpf-fold xs) (vpf-fold ys))))
  :hints (("Goal" :induct (vpf-fold xs) :in-theory (enable vpf-fold vpf-all-carrierp))))

(defun vpf-flatten-blocks (blocks)
  (if (endp blocks) nil
    (append (car blocks) (vpf-flatten-blocks (cdr blocks)))))
(defun vpf-fold-blocks (blocks)
  (if (endp blocks) (vpf-id)
    (vpf-op (vpf-fold (car blocks))
            (vpf-fold-blocks (cdr blocks)))))

(defthm vpf-fold-blocks-correct
  (implies (vpf-all-carrierp (vpf-flatten-blocks blocks))
           (equal (vpf-fold-blocks blocks)
                  (vpf-fold (vpf-flatten-blocks blocks))))
  :hints (("Goal" :induct (vpf-fold-blocks blocks)
           :in-theory (enable vpf-fold-blocks vpf-flatten-blocks))))

; Additive functional instance.
(defun vpf-nump (x) (acl2-numberp x))
(defun vpf-add (x y) (+ x y))
(defun vpf-zero () 0)
(defun vpf-all-nump (xs)
  (if (endp xs) t
    (and (vpf-nump (car xs)) (vpf-all-nump (cdr xs)))))
(defun vpf-sum (xs)
  (if (endp xs) (vpf-zero)
    (vpf-add (car xs) (vpf-sum (cdr xs)))))
(defun vpf-sum-blocks (blocks)
  (if (endp blocks) (vpf-zero)
    (vpf-add (vpf-sum (car blocks))
             (vpf-sum-blocks (cdr blocks)))))

(defthm vpf-nump-of-zero (vpf-nump (vpf-zero))
  :hints (("Goal" :in-theory (enable vpf-nump vpf-zero))))
(defthm vpf-nump-of-add
  (implies (and (vpf-nump x) (vpf-nump y))
           (vpf-nump (vpf-add x y)))
  :hints (("Goal" :in-theory (enable vpf-nump vpf-add))))
(defthm vpf-add-associative
  (implies (and (vpf-nump x) (vpf-nump y) (vpf-nump z))
           (equal (vpf-add (vpf-add x y) z)
                  (vpf-add x (vpf-add y z))))
  :hints (("Goal" :in-theory (enable vpf-add))))
(defthm vpf-add-left-identity
  (implies (vpf-nump x) (equal (vpf-add (vpf-zero) x) x))
  :hints (("Goal" :in-theory (enable vpf-add vpf-zero vpf-nump))))
(defthm vpf-add-right-identity
  (implies (vpf-nump x) (equal (vpf-add x (vpf-zero)) x))
  :hints (("Goal" :in-theory (enable vpf-add vpf-zero vpf-nump))))

(def-functional-instance vpf-sum-blocks-correct
  vpf-fold-blocks-correct
  ((vpf-carrierp vpf-nump)
   (vpf-op vpf-add)
   (vpf-id vpf-zero)
   (vpf-all-carrierp vpf-all-nump)
   (vpf-fold vpf-sum)
   (vpf-fold-blocks vpf-sum-blocks)))

(assert-event
 (equal (vpf-sum-blocks '((1 2) (3) nil (4 5))) 15))

(defxdoc vpf-user-interface
  :parents (zlx-certified-parallel-fold)
  :short "Public interface for certified parallel reductions."
  :long "<p>The generic law is <tt>VPF-FOLD-BLOCKS-CORRECT</tt>.  <tt>VPF-SUM-BLOCKS-CORRECT</tt> is generated
  by @(see def-functional-instance).</p>")
