; zsh-verified-patch-composition.lisp
;
; Source-independent composition of the edit scripts from ZYL.  Patches are
; expanded to unit provenance atoms, composed as stream transducers, and
; compacted back to normalized patches.

(in-package "ACL2")

(include-book "zts-structural-rope-patch")

(defxdoc zsh-verified-patch-composition
  :parents (zts-structural-rope-patch)
  :short "Certified source-independent composition of edit scripts."
  :long
  "<p>This book gives the patch calculus its missing composition operator.
  A finite patch denotes a stream transducer followed by an implicit identity
  tail.  Composition is calculated without a concrete source word: source
  provenance and inserted literals are made explicit as unit atoms, the two
  atom streams are fused, and the result is recompiled to a normalized patch.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Unit provenance atoms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zpc-keep-atom () (list :source-keep))
(defun zpc-drop-atom () (list :source-drop))
(defun zpc-insert-atom (value) (list :literal value))

(defun zpc-keep-atom-p (atom)
  (equal atom (zpc-keep-atom)))

(defun zpc-drop-atom-p (atom)
  (equal atom (zpc-drop-atom)))

(defun zpc-insert-atom-p (atom)
  (and (consp atom)
       (equal (car atom) :literal)
       (consp (cdr atom))
       (endp (cddr atom))))

(defun zpc-insert-atom-value (atom)
  (cadr atom))

(defun zpc-repeat-atom (n atom)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons atom (zpc-repeat-atom (1- n) atom))))

(defun zpc-runs-atoms (runs)
  (if (endp runs)
      nil
    (append
     (zpc-repeat-atom (cdar runs)
                      (zpc-insert-atom (caar runs)))
     (zpc-runs-atoms (cdr runs)))))

(defun zpc-instruction-atoms (instruction)
  (cond ((zyp-keep-p instruction)
         (zpc-repeat-atom (zyp-count instruction)
                          (zpc-keep-atom)))
        ((zyp-drop-p instruction)
         (zpc-repeat-atom (zyp-count instruction)
                          (zpc-drop-atom)))
        ((zyp-insert-p instruction)
         (zpc-runs-atoms (zyp-insert-runs instruction)))
        (t nil)))

(defun zpc-patch-atoms (patch)
  (if (endp patch)
      nil
    (append (zpc-instruction-atoms (car patch))
            (zpc-patch-atoms (cdr patch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Atom semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zpc-atoms-transform (atoms source)
  (if (endp atoms)
      (true-list-fix source)
    (let ((atom (car atoms)))
      (cond ((zpc-keep-atom-p atom)
             (if (endp source)
                 (zpc-atoms-transform (cdr atoms) nil)
               (cons (car source)
                     (zpc-atoms-transform (cdr atoms) (cdr source)))))
            ((zpc-drop-atom-p atom)
             (zpc-atoms-transform (cdr atoms)
                                  (if (consp source) (cdr source) nil)))
            ((zpc-insert-atom-p atom)
             (cons (zpc-insert-atom-value atom)
                   (zpc-atoms-transform (cdr atoms) source)))
            (t
             (zpc-atoms-transform (cdr atoms) source))))))

(defun zpc-atoms-okp (atoms source)
  (if (endp atoms)
      t
    (let ((atom (car atoms)))
      (cond ((or (zpc-keep-atom-p atom)
                 (zpc-drop-atom-p atom))
             (and (consp source)
                  (zpc-atoms-okp (cdr atoms) (cdr source))))
            (t
             (zpc-atoms-okp (cdr atoms) source))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Atom composition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zpc-atom-p (atom)
  (or (zpc-keep-atom-p atom)
      (zpc-drop-atom-p atom)
      (zpc-insert-atom-p atom)))

(defun zpc-compose-atoms (first second)
  (declare (xargs :measure (+ (acl2-count first)
                              (acl2-count second))))
  (cond
   ((endp second)
    (true-list-fix first))
   ((not (zpc-atom-p (car second)))
    (zpc-compose-atoms first (cdr second)))
   ((zpc-insert-atom-p (car second))
    (cons (car second)
          (zpc-compose-atoms first (cdr second))))
   ((endp first)
    (cons (car second)
          (zpc-compose-atoms nil (cdr second))))
   ((not (zpc-atom-p (car first)))
    (zpc-compose-atoms (cdr first) second))
   ((zpc-drop-atom-p (car first))
    (cons (car first)
          (zpc-compose-atoms (cdr first) second)))
   ((zpc-keep-atom-p (car second))
    (cons (car first)
          (zpc-compose-atoms (cdr first) (cdr second))))
   ((zpc-drop-atom-p (car second))
    (if (zpc-keep-atom-p (car first))
        (cons (zpc-drop-atom)
              (zpc-compose-atoms (cdr first) (cdr second)))
      (zpc-compose-atoms (cdr first) (cdr second))))
   (t
    (zpc-compose-atoms first (cdr second)))))

(defun zpc-compose-induction (first second source)
  (declare (xargs :measure (+ (acl2-count first)
                              (acl2-count second))))
  (cond
   ((endp second) source)
   ((not (zpc-atom-p (car second)))
    (zpc-compose-induction first (cdr second) source))
   ((zpc-insert-atom-p (car second))
    (zpc-compose-induction first (cdr second) source))
   ((endp first)
    (zpc-compose-induction nil (cdr second)
                           (if (consp source) (cdr source) nil)))
   ((not (zpc-atom-p (car first)))
    (zpc-compose-induction (cdr first) second source))
   ((zpc-drop-atom-p (car first))
    (zpc-compose-induction (cdr first) second
                           (if (consp source) (cdr source) nil)))
   ((zpc-keep-atom-p (car second))
    (zpc-compose-induction
     (cdr first) (cdr second)
     (if (zpc-keep-atom-p (car first))
         (if (consp source) (cdr source) nil)
       source)))
   ((zpc-drop-atom-p (car second))
    (zpc-compose-induction
     (cdr first) (cdr second)
     (if (zpc-keep-atom-p (car first))
         (if (consp source) (cdr source) nil)
       source)))
   (t
    (zpc-compose-induction first (cdr second) source))))

(defthm zpc-transform-of-compose-atoms
  (implies (and (zpc-atoms-okp first source)
                (zpc-atoms-okp
                 second
                 (zpc-atoms-transform first source)))
           (equal (zpc-atoms-transform
                   (zpc-compose-atoms first second)
                   source)
                  (zpc-atoms-transform
                   second
                   (zpc-atoms-transform first source))))
  :hints
  (("Goal"
    :induct (zpc-compose-induction first second source)
    :in-theory
    (enable zpc-compose-induction
            zpc-compose-atoms
            zpc-atom-p
            zpc-atoms-transform))))

(defthm zpc-okp-of-compose-atoms
  (equal (zpc-atoms-okp (zpc-compose-atoms first second) source)
         (and (zpc-atoms-okp first source)
              (zpc-atoms-okp
               second
               (zpc-atoms-transform first source))))
  :hints
  (("Goal"
    :induct (zpc-compose-induction first second source)
    :in-theory
    (enable zpc-compose-induction
            zpc-compose-atoms
            zpc-atom-p
            zpc-atoms-transform
            zpc-atoms-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Recompilation to ordinary patches
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zpc-atom-instruction (atom)
  (cond ((zpc-keep-atom-p atom)
         (zyp-keep 1))
        ((zpc-drop-atom-p atom)
         (zyp-drop 1))
        ((zpc-insert-atom-p atom)
         (zyp-insert
          (list (cons (zpc-insert-atom-value atom) 1))))
        (t (zyp-keep 0))))

(defun zpc-atoms-patch (atoms)
  (if (endp atoms)
      nil
    (cons (zpc-atom-instruction (car atoms))
          (zpc-atoms-patch (cdr atoms)))))

(defun zpc-patch-transform (patch source)
  (append (zyp-patch-output patch source)
          (zyp-patch-rest patch source)))

(defthm zpc-transform-of-atoms-patch
  (equal (zpc-patch-transform (zpc-atoms-patch atoms) source)
         (zpc-atoms-transform atoms source))
  :hints
  (("Goal"
    :induct (zpc-atoms-transform atoms source)
    :in-theory
    (enable zpc-atoms-patch
            zpc-atom-instruction
            zpc-patch-transform
            zyp-patch-output
            zyp-patch-rest
            zyp-step-output
            zyp-step-rest
            zyp-take
            zyp-drop-prefix
            xef-rle-decode
            xef-repeat))))

(defthm zpc-okp-of-atoms-patch
  (equal (zyp-patch-okp (zpc-atoms-patch atoms) source)
         (zpc-atoms-okp atoms source))
  :hints
  (("Goal"
    :induct (zpc-atoms-okp atoms source)
    :in-theory
    (enable zpc-atoms-patch
            zpc-atom-instruction
            zpc-atoms-okp
            zyp-patch-okp
            zyp-step-okp
            zyp-step-rest
            zyp-enoughp
            zyp-drop-prefix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Expansion algebra for literal atoms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zpc-transform-of-nil-atoms
  (equal (zpc-atoms-transform nil source)
         (true-list-fix source))
  :hints (("Goal" :in-theory (enable zpc-atoms-transform))))

(defthm zpc-okp-of-nil-atoms
  (zpc-atoms-okp nil source)
  :hints (("Goal" :in-theory (enable zpc-atoms-okp))))

(defthm zpc-transform-of-repeat-keep-atom
  (equal (zpc-atoms-transform
          (zpc-repeat-atom n (zpc-keep-atom))
          source)
         (true-list-fix source))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            zyp-drop-prefix))))

(defthm zpc-transform-of-repeat-drop-atom
  (equal (zpc-atoms-transform
          (zpc-repeat-atom n (zpc-drop-atom))
          source)
         (true-list-fix (zyp-drop-prefix n source)))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            zyp-drop-prefix))))

(defthm zpc-okp-of-repeat-keep-atom
  (equal (zpc-atoms-okp
          (zpc-repeat-atom n (zpc-keep-atom))
          source)
         (zyp-enoughp n source))
  :hints
  (("Goal"
    :induct (zyp-enoughp n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-okp
            zyp-enoughp))))

(defthm zpc-okp-of-repeat-drop-atom
  (equal (zpc-atoms-okp
          (zpc-repeat-atom n (zpc-drop-atom))
          source)
         (zyp-enoughp n source))
  :hints
  (("Goal"
    :induct (zyp-enoughp n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-okp
            zyp-enoughp))))

(defthm zpc-transform-of-repeat-insert-atom
  (equal (zpc-atoms-transform
          (zpc-repeat-atom n (zpc-insert-atom value))
          source)
         (append (xef-repeat n value)
                 (true-list-fix source)))
  :hints
  (("Goal"
    :induct (zpc-repeat-atom n (zpc-insert-atom value))
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            xef-repeat))))

(defthm zpc-transform-of-append-repeat-insert-atom
  (equal (zpc-atoms-transform
          (append (zpc-repeat-atom n (zpc-insert-atom value))
                  tail)
          source)
         (append (xef-repeat n value)
                 (zpc-atoms-transform tail source)))
  :hints
  (("Goal"
    :induct (zpc-repeat-atom n (zpc-insert-atom value))
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            xef-repeat))))

(defthm zpc-okp-of-append-repeat-insert-atom
  (equal (zpc-atoms-okp
          (append (zpc-repeat-atom n (zpc-insert-atom value))
                  tail)
          source)
         (zpc-atoms-okp tail source))
  :hints
  (("Goal"
    :induct (zpc-repeat-atom n (zpc-insert-atom value))
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-okp))))

(defthm zpc-transform-of-runs-atoms
  (equal (zpc-atoms-transform (zpc-runs-atoms runs) source)
         (append (xef-rle-decode runs)
                 (true-list-fix source)))
  :hints
  (("Goal"
    :induct (zpc-runs-atoms runs)
    :in-theory
    (e/d (zpc-runs-atoms
          xef-rle-decode)
         (zpc-atoms-transform
          zpc-repeat-atom
          zpc-transform-of-append-repeat-insert-atom)))
   ("Subgoal *1/2"
    :use ((:instance zpc-transform-of-append-repeat-insert-atom
                     (n (cdar runs))
                     (value (caar runs))
                     (tail (zpc-runs-atoms (cdr runs)))
                     (source source))))
   ("Subgoal *1/1"
    :in-theory (enable zpc-atoms-transform))))

(defthm zpc-okp-of-runs-atoms
  (zpc-atoms-okp (zpc-runs-atoms runs) source)
  :hints
  (("Goal"
    :induct (zpc-runs-atoms runs)
    :in-theory
    (e/d (zpc-runs-atoms)
         (zpc-atoms-okp
          zpc-repeat-atom
          zpc-okp-of-append-repeat-insert-atom)))
   ("Subgoal *1/2"
    :use ((:instance zpc-okp-of-append-repeat-insert-atom
                     (n (cdar runs))
                     (value (caar runs))
                     (tail (zpc-runs-atoms (cdr runs)))
                     (source source))))
   ("Subgoal *1/1"
    :in-theory (enable zpc-atoms-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Expansion preserves patch semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zpc-transform-of-append-repeat-keep-atom
  (equal (zpc-atoms-transform
          (append (zpc-repeat-atom n (zpc-keep-atom)) tail)
          source)
         (append (zyp-take n source)
                 (zpc-atoms-transform
                  tail
                  (zyp-drop-prefix n source))))
  :hints
  (("Goal"
    :induct (zyp-take n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            zyp-take
            zyp-drop-prefix))))

(defthm zpc-transform-of-append-repeat-drop-atom
  (equal (zpc-atoms-transform
          (append (zpc-repeat-atom n (zpc-drop-atom)) tail)
          source)
         (zpc-atoms-transform
          tail
          (zyp-drop-prefix n source)))
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-transform
            zyp-drop-prefix))))

(defthm zpc-okp-of-append-repeat-keep-atom
  (equal (zpc-atoms-okp
          (append (zpc-repeat-atom n (zpc-keep-atom)) tail)
          source)
         (and (zyp-enoughp n source)
              (zpc-atoms-okp
               tail
               (zyp-drop-prefix n source))))
  :hints
  (("Goal"
    :induct (zyp-enoughp n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-okp
            zpc-atoms-transform
            zyp-enoughp
            zyp-drop-prefix))))

(defthm zpc-okp-of-append-repeat-drop-atom
  (equal (zpc-atoms-okp
          (append (zpc-repeat-atom n (zpc-drop-atom)) tail)
          source)
         (and (zyp-enoughp n source)
              (zpc-atoms-okp
               tail
               (zyp-drop-prefix n source))))
  :hints
  (("Goal"
    :induct (zyp-enoughp n source)
    :in-theory
    (enable zpc-repeat-atom
            zpc-atoms-okp
            zpc-atoms-transform
            zyp-enoughp
            zyp-drop-prefix))))

(defthm zpc-transform-of-append-runs-atoms
  (equal (zpc-atoms-transform
          (append (zpc-runs-atoms runs) tail)
          source)
         (append (xef-rle-decode runs)
                 (zpc-atoms-transform tail source)))
  :hints
  (("Goal"
    :induct (zpc-runs-atoms runs)
    :in-theory
    (e/d (zpc-runs-atoms
          xef-rle-decode)
         (zpc-atoms-transform
          zpc-repeat-atom
          zpc-transform-of-append-repeat-insert-atom)))
   ("Subgoal *1/2"
    :use ((:instance zpc-transform-of-append-repeat-insert-atom
                     (n (cdar runs))
                     (value (caar runs))
                     (tail (append (zpc-runs-atoms (cdr runs)) tail))
                     (source source))))
   ("Subgoal *1/1"
    :in-theory (enable zpc-atoms-transform))))

(defthm zpc-okp-of-append-runs-atoms
  (equal (zpc-atoms-okp
          (append (zpc-runs-atoms runs) tail)
          source)
         (zpc-atoms-okp tail source))
  :hints
  (("Goal"
    :induct (zpc-runs-atoms runs)
    :in-theory
    (e/d (zpc-runs-atoms)
         (zpc-atoms-okp
          zpc-repeat-atom
          zpc-okp-of-append-repeat-insert-atom)))
   ("Subgoal *1/2"
    :use ((:instance zpc-okp-of-append-repeat-insert-atom
                     (n (cdar runs))
                     (value (caar runs))
                     (tail (append (zpc-runs-atoms (cdr runs)) tail))
                     (source source))))
   ("Subgoal *1/1"
    :in-theory (enable zpc-atoms-okp))))

(defthm zpc-transform-of-append-instruction-atoms
  (equal (zpc-atoms-transform
          (append (zpc-instruction-atoms instruction) tail)
          source)
         (append (zyp-step-output instruction source)
                 (zpc-atoms-transform
                  tail
                  (zyp-step-rest instruction source))))
  :hints
  (("Goal"
    :cases ((zyp-keep-p instruction)
            (zyp-drop-p instruction)
            (zyp-insert-p instruction))
    :use ((:instance zpc-transform-of-append-repeat-keep-atom
                     (n (zyp-count instruction))
                     (tail tail)
                     (source source))
          (:instance zpc-transform-of-append-repeat-drop-atom
                     (n (zyp-count instruction))
                     (tail tail)
                     (source source))
          (:instance zpc-transform-of-append-runs-atoms
                     (runs (zyp-insert-runs instruction))
                     (tail tail)
                     (source source)))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-output
          zyp-step-rest)
         (zpc-atoms-transform
          zpc-repeat-atom
          zpc-runs-atoms
          zpc-transform-of-append-repeat-keep-atom
          zpc-transform-of-append-repeat-drop-atom
          zpc-transform-of-append-runs-atoms)))))

(defthm zpc-okp-of-append-instruction-atoms
  (equal (zpc-atoms-okp
          (append (zpc-instruction-atoms instruction) tail)
          source)
         (and (zyp-step-okp instruction source)
              (zpc-atoms-okp
               tail
               (zyp-step-rest instruction source))))
  :hints
  (("Goal"
    :cases ((zyp-keep-p instruction)
            (zyp-drop-p instruction)
            (zyp-insert-p instruction))
    :use ((:instance zpc-okp-of-append-repeat-keep-atom
                     (n (zyp-count instruction))
                     (tail tail)
                     (source source))
          (:instance zpc-okp-of-append-repeat-drop-atom
                     (n (zyp-count instruction))
                     (tail tail)
                     (source source))
          (:instance zpc-okp-of-append-runs-atoms
                     (runs (zyp-insert-runs instruction))
                     (tail tail)
                     (source source)))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-okp
          zyp-step-rest)
         (zpc-atoms-okp
          zpc-repeat-atom
          zpc-runs-atoms
          zpc-okp-of-append-repeat-keep-atom
          zpc-okp-of-append-repeat-drop-atom
          zpc-okp-of-append-runs-atoms)))))

(defthm zpc-transform-of-expanded-keep
  (implies (zyp-keep-p instruction)
           (equal (zpc-atoms-transform
                   (zpc-instruction-atoms instruction)
                   source)
                  (append (zyp-step-output instruction source)
                          (true-list-fix
                           (zyp-step-rest instruction source)))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-repeat-keep-atom
                     (n (zyp-count instruction)))
          (:instance zyp-append-take-and-drop
                     (n (zyp-count instruction))
                     (xs source)))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-output
          zyp-step-rest)
         (zpc-atoms-transform
          zpc-repeat-atom
          zpc-transform-of-repeat-keep-atom
          zyp-append-take-and-drop)))))

(defthm zpc-transform-of-expanded-drop
  (implies (zyp-drop-p instruction)
           (equal (zpc-atoms-transform
                   (zpc-instruction-atoms instruction)
                   source)
                  (append (zyp-step-output instruction source)
                          (true-list-fix
                           (zyp-step-rest instruction source)))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-repeat-drop-atom
                     (n (zyp-count instruction))))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-output
          zyp-step-rest)
         (zpc-atoms-transform
          zpc-repeat-atom
          zpc-transform-of-repeat-drop-atom)))))

(defthm zpc-transform-of-expanded-insert
  (implies (zyp-insert-p instruction)
           (equal (zpc-atoms-transform
                   (zpc-instruction-atoms instruction)
                   source)
                  (append (zyp-step-output instruction source)
                          (true-list-fix
                           (zyp-step-rest instruction source)))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-runs-atoms
                     (runs (zyp-insert-runs instruction))))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-output
          zyp-step-rest)
         (zpc-atoms-transform
          zpc-runs-atoms
          zpc-transform-of-runs-atoms)))))

(defthm zpc-transform-of-expanded-malformed
  (implies (and (not (zyp-keep-p instruction))
                (not (zyp-drop-p instruction))
                (not (zyp-insert-p instruction)))
           (equal (zpc-atoms-transform
                   (zpc-instruction-atoms instruction)
                   source)
                  (append (zyp-step-output instruction source)
                          (true-list-fix
                           (zyp-step-rest instruction source)))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-nil-atoms))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-output
          zyp-step-rest)
         (zpc-atoms-transform
          zpc-transform-of-nil-atoms)))))

(defthm zpc-transform-of-expanded-instruction
  (equal (zpc-atoms-transform
          (zpc-instruction-atoms instruction)
          source)
         (append (zyp-step-output instruction source)
                 (true-list-fix
                  (zyp-step-rest instruction source))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-expanded-keep)
          (:instance zpc-transform-of-expanded-drop)
          (:instance zpc-transform-of-expanded-insert)
          (:instance zpc-transform-of-expanded-malformed))
    :in-theory
    (disable zpc-transform-of-expanded-keep
             zpc-transform-of-expanded-drop
             zpc-transform-of-expanded-insert
             zpc-transform-of-expanded-malformed))))

(defthm zpc-transform-of-expanded-patch
  (equal (zpc-atoms-transform (zpc-patch-atoms patch) source)
         (zpc-patch-transform patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-output patch source)
    :in-theory
    (e/d (zpc-patch-atoms
          zpc-patch-transform
          zyp-patch-output
          zyp-patch-rest)
         (zpc-atoms-transform
          zpc-instruction-atoms)))))

(defthm zpc-okp-of-expanded-keep
  (implies (zyp-keep-p instruction)
           (equal (zpc-atoms-okp
                   (zpc-instruction-atoms instruction)
                   source)
                  (zyp-step-okp instruction source)))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-repeat-keep-atom
                     (n (zyp-count instruction))))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-okp)
         (zpc-atoms-okp
          zpc-repeat-atom
          zpc-okp-of-repeat-keep-atom)))))

(defthm zpc-okp-of-expanded-drop
  (implies (zyp-drop-p instruction)
           (equal (zpc-atoms-okp
                   (zpc-instruction-atoms instruction)
                   source)
                  (zyp-step-okp instruction source)))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-repeat-drop-atom
                     (n (zyp-count instruction))))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-okp)
         (zpc-atoms-okp
          zpc-repeat-atom
          zpc-okp-of-repeat-drop-atom)))))

(defthm zpc-okp-of-expanded-insert
  (implies (zyp-insert-p instruction)
           (equal (zpc-atoms-okp
                   (zpc-instruction-atoms instruction)
                   source)
                  (zyp-step-okp instruction source)))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-runs-atoms
                     (runs (zyp-insert-runs instruction))))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-okp)
         (zpc-atoms-okp
          zpc-runs-atoms
          zpc-okp-of-runs-atoms)))))

(defthm zpc-okp-of-expanded-malformed
  (implies (and (not (zyp-keep-p instruction))
                (not (zyp-drop-p instruction))
                (not (zyp-insert-p instruction)))
           (equal (zpc-atoms-okp
                   (zpc-instruction-atoms instruction)
                   source)
                  (zyp-step-okp instruction source)))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-nil-atoms))
    :in-theory
    (e/d (zpc-instruction-atoms
          zyp-step-okp)
         (zpc-atoms-okp
          zpc-okp-of-nil-atoms)))))

(defthm zpc-okp-of-expanded-instruction
  (equal (zpc-atoms-okp
          (zpc-instruction-atoms instruction)
          source)
         (zyp-step-okp instruction source))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-expanded-keep)
          (:instance zpc-okp-of-expanded-drop)
          (:instance zpc-okp-of-expanded-insert)
          (:instance zpc-okp-of-expanded-malformed))
    :in-theory
    (disable zpc-okp-of-expanded-keep
             zpc-okp-of-expanded-drop
             zpc-okp-of-expanded-insert
             zpc-okp-of-expanded-malformed))))

(defthm zpc-okp-of-expanded-patch
  (equal (zpc-atoms-okp (zpc-patch-atoms patch) source)
         (zyp-patch-okp patch source))
  :hints
  (("Goal"
    :induct (zyp-patch-okp patch source)
    :in-theory
    (e/d (zpc-patch-atoms
          zyp-patch-okp)
         (zpc-atoms-okp
          zpc-instruction-atoms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 7. Public composition operation and laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zpc-compose (first second)
  (zyp-normalize
   (zpc-atoms-patch
    (zpc-compose-atoms
     (zpc-patch-atoms first)
     (zpc-patch-atoms second)))))

(defthm zpc-compose-transform-correct
  (implies (and (zyp-patch-okp first source)
                (zyp-patch-okp
                 second
                 (zpc-patch-transform first source)))
           (equal (zpc-patch-transform
                   (zpc-compose first second)
                   source)
                  (zpc-patch-transform
                   second
                   (zpc-patch-transform first source))))
  :hints
  (("Goal"
    :use ((:instance zpc-transform-of-atoms-patch
                     (atoms (zpc-compose-atoms
                             (zpc-patch-atoms first)
                             (zpc-patch-atoms second))))
          (:instance zpc-transform-of-compose-atoms
                     (first (zpc-patch-atoms first))
                     (second (zpc-patch-atoms second)))
          (:instance zpc-transform-of-expanded-patch
                     (patch first))
          (:instance zpc-transform-of-expanded-patch
                     (patch second)
                     (source (zpc-patch-transform first source))))
    :in-theory
    (e/d (zpc-compose
          zpc-patch-transform)
         (zpc-transform-of-atoms-patch
          zpc-transform-of-compose-atoms
          zpc-transform-of-expanded-patch)))))

(defthm zpc-compose-okp-correct
  (equal (zyp-patch-okp (zpc-compose first second) source)
         (and (zyp-patch-okp first source)
              (zyp-patch-okp
               second
               (zpc-patch-transform first source))))
  :hints
  (("Goal"
    :use ((:instance zpc-okp-of-atoms-patch
                     (atoms (zpc-compose-atoms
                             (zpc-patch-atoms first)
                             (zpc-patch-atoms second))))
          (:instance zpc-okp-of-compose-atoms
                     (first (zpc-patch-atoms first))
                     (second (zpc-patch-atoms second)))
          (:instance zpc-okp-of-expanded-patch
                     (patch first))
          (:instance zpc-okp-of-expanded-patch
                     (patch second)
                     (source (zpc-patch-transform first source))))
    :in-theory
    (e/d (zpc-compose)
         (zpc-okp-of-atoms-patch
          zpc-okp-of-compose-atoms
          zpc-okp-of-expanded-patch
          zsp-patch-okp-is-source-demand)))))

(defthm zpc-compose-transactional-correct
  (equal (zvr-patch-word (zpc-compose first second) source)
         (if (and (zyp-patch-okp first source)
                  (zyp-patch-okp
                   second
                   (zpc-patch-transform first source)))
             (zvr-patch-word
              second
              (zvr-patch-word first source))
           (true-list-fix source)))
  :hints
  (("Goal"
    :use ((:instance zpc-compose-transform-correct)
          (:instance zpc-compose-okp-correct))
    :in-theory
    (enable zvr-patch-word))))

(defthm zpc-compose-is-canonical
  (zyp-canonical-p (zpc-compose first second))
  :hints
  (("Goal"
    :in-theory (enable zpc-compose))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 8. Ground check
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zpc-first*
  (list (zyp-keep 2)
        (zyp-drop 1)
        (zyp-insert (xef-rle-encode '(x y)))
        (zyp-keep 2)))

(defconst *zpc-second*
  (list (zyp-drop 1)
        (zyp-keep 2)
        (zyp-insert (xef-rle-encode '(q)))
        (zyp-keep 2)))

(assert-event
 (equal (zpc-patch-transform
         (zpc-compose *zpc-first* *zpc-second*)
         '(a b c d e f))
        (zpc-patch-transform
         *zpc-second*
         (zpc-patch-transform *zpc-first* '(a b c d e f)))))

(defxdoc zpc-user-interface
  :parents (zsh-verified-patch-composition)
  :short "The verified patch-composition interface."
  :long
  "<p><tt>ZPC-COMPOSE</tt> accepts two ordinary patches and returns one
  canonical patch.  <tt>ZPC-COMPOSE-TRANSFORM-CORRECT</tt> is the successful
  stream-transducer law; <tt>ZPC-COMPOSE-TRANSACTIONAL-CORRECT</tt> states the
  corresponding atomic transactional law.</p>")
