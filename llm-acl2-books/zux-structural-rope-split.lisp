; zux-structural-rope-split.lisp
;
; Structure-preserving prefix/suffix operations for the binary ropes of ZZE.
; The functions retain every untouched subtree literally and split only along
; one root-to-leaf boundary path.

(in-package "ACL2")

(include-book "zvu-rope-local-patch")

(defxdoc zux-structural-rope-split
  :parents (zvu-rope-local-patch)
  :short "Certified structure-preserving splitting of binary ropes."
  :long
  "<p>This book defines structural TAKE and DROP operations for the binary
  ropes introduced by <tt>ZZE-EXOTIC-FERTILE-KERNEL</tt>.  A split traverses
  only the boundary path: subtrees wholly before or after the boundary are
  reused as complete ACL2 objects.  The principal theorems identify the
  flattened results with the total prefix operations from
  <tt>ZYL-VERIFIED-PATCH-CALCULUS</tt>.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Structural length
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zrs-rope-length (rope)
  (cond ((xef-rope-leaf-p rope)
         (len (true-list-fix (cdr rope))))
        ((xef-rope-cat-p rope)
         (+ (zrs-rope-length (cadr rope))
            (zrs-rope-length (caddr rope))))
        (t 0)))

(defthm zrs-rope-length-refines-flattening
  (equal (zrs-rope-length rope)
         (len (xef-rope-flatten rope)))
  :hints
  (("Goal"
    :induct (zrs-rope-length rope)
    :in-theory
    (enable zrs-rope-length
            xef-rope-flatten))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Total-list algebra used by the rope proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zrs-enoughp-iff-count-at-most-len
  (equal (zyp-enoughp n xs)
         (<= (nfix n) (len xs)))
  :hints
  (("Goal"
    :induct (zyp-enoughp n xs)
    :in-theory (enable zyp-enoughp))))

(defthm zrs-take-when-count-covers-list
  (implies (<= (len xs) (nfix n))
           (equal (zyp-take n xs)
                  (true-list-fix xs)))
  :hints
  (("Goal"
    :induct (zyp-take n xs)
    :in-theory (enable zyp-take true-list-fix))))

(defthm zrs-take-of-append
  (equal (zyp-take n (append xs ys))
         (append (zyp-take n xs)
                 (zyp-take (- (nfix n) (len xs)) ys)))
  :hints
  (("Goal"
    :induct (zyp-take n xs)
    :in-theory (enable zyp-take))))

(defthm zrs-drop-prefix-of-append
  (equal (zyp-drop-prefix n (append xs ys))
         (if (< (nfix n) (len xs))
             (append (zyp-drop-prefix n xs) ys)
           (zyp-drop-prefix (- (nfix n) (len xs)) ys)))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n xs)
    :in-theory (enable zyp-drop-prefix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Structure-preserving rope prefix and suffix
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zrs-rope-take (n rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond ((zp n)
         (xef-rope-leaf nil))
        ((xef-rope-leaf-p rope)
         (xef-rope-leaf (zyp-take n (cdr rope))))
        ((xef-rope-cat-p rope)
         (let* ((left (cadr rope))
                (right (caddr rope))
                (left-length (zrs-rope-length left)))
           (if (<= (nfix n) left-length)
               (zrs-rope-take n left)
             (xef-rope-cat
              left
              (zrs-rope-take (- (nfix n) left-length)
                             right)))))
        (t
         (xef-rope-leaf nil))))

(defun zrs-rope-drop (n rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond ((zp n)
         rope)
        ((xef-rope-leaf-p rope)
         (xef-rope-leaf (zyp-drop-prefix n (cdr rope))))
        ((xef-rope-cat-p rope)
         (let* ((left (cadr rope))
                (right (caddr rope))
                (left-length (zrs-rope-length left)))
           (if (< (nfix n) left-length)
               (xef-rope-cat
                (zrs-rope-drop n left)
                right)
             (zrs-rope-drop (- (nfix n) left-length)
                            right))))
        (t
         (xef-rope-leaf nil))))

(defun zrs-rope-split (n rope)
  (cons (zrs-rope-take n rope)
        (zrs-rope-drop n rope)))

(defun zrs-split-prefix (split)
  (car split))

(defun zrs-split-suffix (split)
  (cdr split))

(defthm zrs-flatten-of-rope-take
  (equal (xef-rope-flatten (zrs-rope-take n rope))
         (zyp-take n (xef-rope-flatten rope)))
  :hints
  (("Goal"
    :induct (zrs-rope-take n rope)
    :in-theory
    (enable zrs-rope-take
            zrs-rope-length-refines-flattening))))

(defthm zrs-flatten-of-rope-drop
  (equal (xef-rope-flatten (zrs-rope-drop n rope))
         (true-list-fix
          (zyp-drop-prefix n (xef-rope-flatten rope))))
  :hints
  (("Goal"
    :induct (zrs-rope-drop n rope)
    :in-theory
    (enable zrs-rope-drop
            zrs-rope-length-refines-flattening))))

(defthm zrs-flatten-of-split-prefix
  (equal (xef-rope-flatten
          (zrs-split-prefix (zrs-rope-split n rope)))
         (zyp-take n (xef-rope-flatten rope)))
  :hints (("Goal" :in-theory (enable zrs-rope-split zrs-split-prefix))))

(defthm zrs-flatten-of-split-suffix
  (equal (xef-rope-flatten
          (zrs-split-suffix (zrs-rope-split n rope)))
         (true-list-fix
          (zyp-drop-prefix n (xef-rope-flatten rope))))
  :hints (("Goal" :in-theory (enable zrs-rope-split zrs-split-suffix))))

(defthm zrs-split-reconstructs-word
  (equal (append
          (xef-rope-flatten
           (zrs-split-prefix (zrs-rope-split n rope)))
          (xef-rope-flatten
           (zrs-split-suffix (zrs-rope-split n rope))))
         (xef-rope-flatten rope))
  :hints
  (("Goal"
    :in-theory
    (enable zrs-rope-split
            zrs-split-prefix
            zrs-split-suffix))))

(defthm zrs-summary-of-split-reconstruction
  (equal (xef-bi-join
          (xef-rope-summary
           (zrs-split-prefix (zrs-rope-split n rope)) table)
          (xef-rope-summary
           (zrs-split-suffix (zrs-rope-split n rope)) table))
         (xef-rope-summary rope table))
  :hints
  (("Goal"
    :use ((:instance xef-word-bi-summary-of-append
                     (xs (xef-rope-flatten
                          (zrs-split-prefix (zrs-rope-split n rope))))
                     (ys (xef-rope-flatten
                          (zrs-split-suffix (zrs-rope-split n rope)))))
          (:instance zrs-split-reconstructs-word
                     (n n)
                     (rope rope))
          (:instance xef-rope-summary-refines-flattening
                     (rope rope))
          (:instance xef-rope-summary-refines-flattening
                     (rope (zrs-split-prefix (zrs-rope-split n rope))))
          (:instance xef-rope-summary-refines-flattening
                     (rope (zrs-split-suffix (zrs-rope-split n rope)))))
    :in-theory
    (e/d ()
         (xef-word-bi-summary-of-append
          zrs-split-reconstructs-word
          xef-rope-summary-refines-flattening
          xef-word-bi-summary
          xef-bi-join
          xef-bi-summary
          xef-cocycle-compose
          xef-cocycle-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Ground check
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zrs-demo-rope*
  (xef-rope-cat
   (xef-rope-cat
    (xef-rope-leaf '(a b))
    (xef-rope-leaf '(c d e)))
   (xef-rope-leaf '(f g))))

(assert-event
 (and (equal (xef-rope-flatten
              (zrs-split-prefix
               (zrs-rope-split 4 *zrs-demo-rope*)))
             '(a b c d))
      (equal (xef-rope-flatten
              (zrs-split-suffix
               (zrs-rope-split 4 *zrs-demo-rope*)))
             '(e f g))))

(defxdoc zrs-user-interface
  :parents (zux-structural-rope-split)
  :short "The structural rope-splitting interface."
  :long
  "<p><tt>ZRS-ROPE-TAKE</tt> and <tt>ZRS-ROPE-DROP</tt> retain complete
  subtrees away from the split boundary.  <tt>ZRS-ROPE-SPLIT</tt> packages
  both results; use <tt>ZRS-SPLIT-PREFIX</tt> and
  <tt>ZRS-SPLIT-SUFFIX</tt> to project them.</p>")
