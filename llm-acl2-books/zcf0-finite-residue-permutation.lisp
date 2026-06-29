; Finite positive-residue permutations and their positional inverse.
(in-package "ACL2")

(include-book "zbf-rader-index-certificate")
(include-book "kestrel/utilities/lists/index-of-theorems" :dir :system)
(include-book "kestrel/lists-light/subsetp-equal" :dir :system)

(defun zcf-positive-countdown (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons count
          (zcf-positive-countdown (1- count)))))

(defthm len-of-zcf-positive-countdown
  (equal (len (zcf-positive-countdown count))
         (nfix count))
  :hints (("Goal" :induct (zcf-positive-countdown count)
           :in-theory (enable zcf-positive-countdown))))

(defthm member-of-zcf-positive-countdown
  (iff (member-equal x (zcf-positive-countdown count))
       (and (posp x)
            (<= x (nfix count))))
  :hints (("Goal" :induct (zcf-positive-countdown count)
           :in-theory (enable zcf-positive-countdown posp))))

(defthm zcf-positive-below-p-member-countdown
  (implies (and (posp x)
                (< x (nfix p)))
           (member-equal
            x
            (zcf-positive-countdown (1- (nfix p)))))
  :hints
  (("Goal"
    :use ((:instance member-of-zcf-positive-countdown
                     (count (1- (nfix p)))))
    :in-theory (enable posp))))

(defthm zcf-positive-residues-subset-countdown
  (implies (rgi-positive-residuesp p xs)
           (subsetp-equal
            xs
            (zcf-positive-countdown (1- (nfix p)))))
  :hints
  (("Goal"
    :induct (rgi-positive-residuesp p xs)
    :in-theory
    (enable rgi-positive-residuesp
            subsetp-equal
            zcf-positive-below-p-member-countdown))))

(defthm zcf-subsetp-equal-of-cons
  (implies (and (member-equal x ys)
                (subsetp-equal xs ys))
           (subsetp-equal (cons x xs) ys))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm zcf-no-duplicatesp-equal-of-cons
  (implies (and (not (member-equal x xs))
                (no-duplicatesp-equal xs))
           (no-duplicatesp-equal (cons x xs)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(defthm zcf-strict-len-when-adjoining-new-subset-member
  (implies (and (member-equal x ys)
                (subsetp-equal xs ys)
                (not (member-equal x xs))
                (no-duplicatesp-equal xs))
           (< (len xs) (len ys)))
  :hints
  (("Goal"
    :use
    ((:instance zcf-subsetp-equal-of-cons)
     (:instance zcf-no-duplicatesp-equal-of-cons)
     (:instance
      <=-of-len-and-len-when-subsetp-equal-and-no-duplicatesp-equal
      (x (cons x xs))
      (y ys)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(len-of-cons)))))

(defthm zcf-member-of-full-positive-residue-list
  (implies
   (and (rgi-positive-residuesp p xs)
        (no-duplicatesp-equal xs)
        (equal (len xs) (1- (nfix p)))
        (posp x)
        (< x (nfix p)))
   (member-equal x xs))
  :hints
  (("Goal"
    :cases ((member-equal x xs))
    :use
    ((:instance zcf-positive-residues-subset-countdown)
     (:instance zcf-positive-below-p-member-countdown)
     (:instance zcf-strict-len-when-adjoining-new-subset-member
                (ys (zcf-positive-countdown (1- (nfix p)))))
     (:instance len-of-zcf-positive-countdown
                (count (1- (nfix p)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(natp nfix posp)))))

(defthm zcf-member-of-rgi-permutation
  (implies (and (rgi-permutationp p xs)
                (posp x)
                (< x (nfix p)))
           (member-equal x xs))
  :hints (("Goal"
           :use ((:instance zcf-member-of-full-positive-residue-list))
           :in-theory (enable rgi-permutationp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A clean positional inverse, defined before the generated Toom rules enter.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zcf-nat-listp (xs)
  (if (endp xs)
      t
    (and (natp (car xs))
         (zcf-nat-listp (cdr xs)))))

(defthm zcf-positive-residues-imply-nat-listp
  (implies (rgi-positive-residuesp p xs)
           (zcf-nat-listp xs))
  :hints (("Goal"
           :induct (rgi-positive-residuesp p xs)
           :in-theory (enable rgi-positive-residuesp
                              zcf-nat-listp posp natp))))

(defun zcf-position (x xs)
  (if (endp xs)
      0
    (if (equal (nfix x) (nfix (car xs)))
        0
      (1+ (zcf-position x (cdr xs))))))

(defun zcf-nth-induct (i xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (or (endp xs) (zp i))
      (list i xs)
    (zcf-nth-induct (1- i) (cdr xs))))

(defthm zcf-natp-of-nth-when-nat-listp
  (implies (and (zcf-nat-listp xs)
                (natp i)
                (< i (len xs)))
           (natp (nth i xs)))
  :hints (("Goal"
           :induct (zcf-nth-induct i xs)
           :in-theory (enable zcf-nth-induct zcf-nat-listp
                              nth len natp zp))))

(defthm zcf-position-is-index-of
  (implies (and (natp x)
                (zcf-nat-listp xs)
                (member-equal x xs))
           (equal (zcf-position x xs)
                  (index-of x xs)))
  :hints (("Goal"
           :induct (zcf-position x xs)
           :in-theory (enable zcf-position index-of member-equal
                              zcf-nat-listp nfix natp))))

(defthm zcf-position-of-nth
  (implies (and (natp i)
                (< i (len xs))
                (zcf-nat-listp xs)
                (no-duplicatesp-equal xs))
           (equal (zcf-position (nth i xs) xs)
                  i))
  :hints
  (("Goal"
    :use ((:instance zcf-natp-of-nth-when-nat-listp)
          (:instance index-of-nth-when-no-duplicatesp
                     (x xs)))
    :in-theory (enable zcf-position-is-index-of integer-range-p))))

(defthm zcf-nth-of-position
  (implies (and (natp x)
                (zcf-nat-listp xs)
                (member-equal x xs))
           (equal (nth (zcf-position x xs) xs)
                  x))
  :hints
  (("Goal"
    :use ((:instance nth-of-index-when-member
                     (k x) (x xs)))
    :in-theory (enable zcf-position-is-index-of))))

(defthm zcf-position-less-than-len
  (implies (and (natp x)
                (zcf-nat-listp xs)
                (member-equal x xs))
           (< (zcf-position x xs) (len xs)))
  :rule-classes :linear
  :hints
  (("Goal"
    :use ((:instance index-of-<-len (k x) (x xs)))
    :in-theory (enable zcf-position-is-index-of))))

(defthm zcf-positive-residue-of-nth
  (implies (and (rgi-positive-residuesp p xs)
                (natp i)
                (< i (len xs)))
           (and (posp (nth i xs))
                (< (nth i xs) (nfix p))))
  :hints
  (("Goal"
    :induct (zcf-nth-induct i xs)
    :in-theory
    (enable zcf-nth-induct rgi-positive-residuesp
            nth len natp zp))))

(defthm zcf-permutation-residue-of-nth
  (implies (and (rgi-permutationp p xs)
                (natp i)
                (< i (len xs)))
           (and (posp (nth i xs))
                (< (nth i xs) (nfix p))))
  :hints
  (("Goal"
    :use ((:instance zcf-positive-residue-of-nth))
    :in-theory (enable rgi-permutationp))))

(defthm zcf-position-zero-in-positive-residues
  (implies (rgi-positive-residuesp p xs)
           (equal (zcf-position 0 xs)
                  (len xs)))
  :hints
  (("Goal"
    :induct (rgi-positive-residuesp p xs)
    :in-theory
    (enable rgi-positive-residuesp zcf-position len posp nfix))))

(defthm zcf-natp-of-position
  (natp (zcf-position x xs))
  :hints
  (("Goal"
    :induct (zcf-position x xs)
    :in-theory (enable zcf-position natp))))
