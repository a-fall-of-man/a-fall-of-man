; zts-structural-rope-patch.lisp
;
; Transactional edit scripts executed directly over binary ropes.  Source
; words are never flattened by the executable functions in this book.

(in-package "ACL2")

(include-book "zux-structural-rope-split")

(defxdoc zts-structural-rope-patch
  :parents (zux-structural-rope-split)
  :short "Verified edit scripts that consume and summarize ropes structurally."
  :long
  "<p>This book lifts the patch calculus of
  <tt>ZYL-VERIFIED-PATCH-CALCULUS</tt> from lists to binary ropes.  KEEP and
  DROP use the certified structural split operations of
  <tt>ZUX-STRUCTURAL-ROPE-SPLIT</tt>; INSERT constructs a leaf from its canonical
  RLE payload.  Untouched source subtrees survive as literal subobjects.</p>

  <p>A parallel summary compiler consumes the rope structurally and compiles
  inserted RLE runs without decoding them.  The principal theorems identify
  the rope execution and summary with the earlier list semantics.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Static success criterion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm zsp-patch-okp-is-source-demand
  (equal (zyp-patch-okp patch source)
         (zyp-enoughp (zyp-source-demand patch) source))
  :hints
  (("Goal"
    :induct (zyp-patch-okp patch source)
    :in-theory
    (enable zyp-patch-okp
            zyp-source-demand
            zyp-step-okp
            zyp-step-rest))))

(defun zsp-patch-rope-okp (patch source-rope)
  (<= (zyp-source-demand patch)
      (zrs-rope-length source-rope)))

(defthm zsp-patch-rope-okp-refines-list-semantics
  (equal (zsp-patch-rope-okp patch source-rope)
         (zyp-patch-okp patch (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :in-theory
    (enable zsp-patch-rope-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Structural instruction and patch execution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zsp-empty-rope ()
  (xef-rope-leaf nil))

(defun zsp-step-rope-rest (instruction source-rope)
  (cond ((zyp-keep-p instruction)
         (zrs-rope-drop (zyp-count instruction) source-rope))
        ((zyp-drop-p instruction)
         (zrs-rope-drop (zyp-count instruction) source-rope))
        (t source-rope)))

(defun zsp-step-rope-output (instruction source-rope)
  (cond ((zyp-keep-p instruction)
         (zrs-rope-take (zyp-count instruction) source-rope))
        ((zyp-insert-p instruction)
         (xef-rope-leaf
          (xef-rle-decode (zyp-insert-runs instruction))))
        (t (zsp-empty-rope))))

(defun zsp-patch-rope-rest (patch source-rope)
  (if (endp patch)
      source-rope
    (zsp-patch-rope-rest
     (cdr patch)
     (zsp-step-rope-rest (car patch) source-rope))))

(defun zsp-patch-rope-output (patch source-rope)
  (if (endp patch)
      (zsp-empty-rope)
    (xef-rope-cat
     (zsp-step-rope-output (car patch) source-rope)
     (zsp-patch-rope-output
      (cdr patch)
      (zsp-step-rope-rest (car patch) source-rope)))))

(defun zsp-patch-rope (patch source-rope)
  (if (zsp-patch-rope-okp patch source-rope)
      (xef-rope-cat
       (zsp-patch-rope-output patch source-rope)
       (zsp-patch-rope-rest patch source-rope))
    source-rope))

(defthm zsp-true-listp-of-rle-decode
  (true-listp (xef-rle-decode runs))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :induct (xef-rle-decode runs)
    :in-theory (enable xef-rle-decode xef-repeat))))

(defthm zsp-flatten-of-empty-rope
  (equal (xef-rope-flatten (zsp-empty-rope))
         nil)
  :hints (("Goal" :in-theory (enable zsp-empty-rope))))

(defthm zsp-flatten-of-step-rope-rest
  (equal (xef-rope-flatten
          (zsp-step-rope-rest instruction source-rope))
         (true-list-fix
          (zyp-step-rest instruction
                         (xef-rope-flatten source-rope))))
  :hints
  (("Goal"
    :in-theory
    (enable zsp-step-rope-rest
            zyp-step-rest))))

(defthm zsp-flatten-of-step-rope-output
  (equal (xef-rope-flatten
          (zsp-step-rope-output instruction source-rope))
         (zyp-step-output instruction
                          (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :in-theory
    (enable zsp-step-rope-output
            zsp-empty-rope
            zyp-step-output))))

(defthm zsp-flatten-of-patch-rope-rest
  (equal (xef-rope-flatten
          (zsp-patch-rope-rest patch source-rope))
         (zyp-patch-rest patch
                         (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :induct (zsp-patch-rope-rest patch source-rope)
    :in-theory
    (enable zsp-patch-rope-rest
            zyp-patch-rest))))

(defthm zsp-flatten-of-patch-rope-output
  (equal (xef-rope-flatten
          (zsp-patch-rope-output patch source-rope))
         (zyp-patch-output patch
                           (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :induct (zsp-patch-rope-output patch source-rope)
    :in-theory
    (enable zsp-patch-rope-output
            zyp-patch-output))))

(defthm zsp-flatten-of-patch-rope
  (equal (xef-rope-flatten
          (zsp-patch-rope patch source-rope))
         (zvr-patch-word patch
                         (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :cases ((zsp-patch-rope-okp patch source-rope))
    :in-theory
    (enable zsp-patch-rope
            zvr-patch-word))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Structural bidirectional summary compilation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zsp-step-rope-output-summary (instruction source-rope table)
  (cond ((zyp-keep-p instruction)
         (xef-rope-summary
          (zrs-rope-take (zyp-count instruction) source-rope)
          table))
        ((zyp-insert-p instruction)
         (zvr-rle-bi-summary (zyp-insert-runs instruction) table))
        (t (xef-bi-empty))))

(defun zsp-patch-rope-output-summary (patch source-rope table)
  (if (endp patch)
      (xef-bi-empty)
    (xef-bi-join
     (zsp-step-rope-output-summary (car patch) source-rope table)
     (zsp-patch-rope-output-summary
      (cdr patch)
      (zsp-step-rope-rest (car patch) source-rope)
      table))))

(defun zsp-patch-rope-summary (patch source-rope table)
  (if (zsp-patch-rope-okp patch source-rope)
      (xef-bi-join
       (zsp-patch-rope-output-summary patch source-rope table)
       (xef-rope-summary
        (zsp-patch-rope-rest patch source-rope)
        table))
    (xef-rope-summary source-rope table)))

(defthm zsp-true-listp-of-rope-flatten
  (true-listp (xef-rope-flatten rope))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :induct (xef-rope-flatten rope)
    :in-theory
    (enable xef-rope-flatten
            xef-rope-leaf-p
            xef-rope-cat-p))))

(defthm zsp-true-listp-of-drop-prefix
  (implies (true-listp source)
           (true-listp (zyp-drop-prefix n source)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :induct (zyp-drop-prefix n source)
    :in-theory (enable zyp-drop-prefix))))

(defthm zsp-flatten-of-step-rope-rest-exact
  (equal (xef-rope-flatten
          (zsp-step-rope-rest instruction source-rope))
         (zyp-step-rest instruction
                        (xef-rope-flatten source-rope)))
  :hints
  (("Goal"
    :use ((:instance zsp-flatten-of-step-rope-rest))
    :in-theory
    (disable zsp-flatten-of-step-rope-rest))))

(defthm zsp-step-rope-output-summary-refines-zvr
  (equal (zsp-step-rope-output-summary instruction source-rope table)
         (zvr-step-output-bi-summary
          instruction
          (xef-rope-flatten source-rope)
          table))
  :hints
  (("Goal"
    :in-theory
    (enable zsp-step-rope-output-summary
            zvr-step-output-bi-summary))))

(defthm zsp-patch-rope-output-summary-refines-zvr
  (equal (zsp-patch-rope-output-summary patch source-rope table)
         (zvr-patch-output-bi-summary
          patch
          (xef-rope-flatten source-rope)
          table))
  :hints
  (("Goal"
    :induct (zsp-patch-rope-output-summary patch source-rope table))
   ("Subgoal *1/2"
    :expand ((zsp-patch-rope-output-summary patch source-rope table)
             (zvr-patch-output-bi-summary
              patch (xef-rope-flatten source-rope) table))
    :use ((:instance zsp-step-rope-output-summary-refines-zvr
                     (instruction (car patch))))
    :in-theory
    (e/d ()
         (zsp-patch-rope-output-summary
          zvr-patch-output-bi-summary
          zsp-step-rope-output-summary
          zvr-step-output-bi-summary
          zsp-step-rope-rest
          xef-rope-flatten
          xef-bi-join
          xef-bi-empty
          xef-bi-join-left-identity
          xef-bi-join-right-identity
          zvr-step-output-bi-summary-refines-output
          zvr-patch-output-bi-summary-refines-output)))
   ("Subgoal *1/1"
    :expand ((zsp-patch-rope-output-summary patch source-rope table)
             (zvr-patch-output-bi-summary
              patch (xef-rope-flatten source-rope) table))
    :in-theory
    (disable xef-bi-empty
             (:executable-counterpart xef-bi-empty)))))

(defthm zsp-patch-rope-output-summary-correct
  (equal (zsp-patch-rope-output-summary patch source-rope table)
         (xef-rope-summary
          (zsp-patch-rope-output patch source-rope)
          table))
  :hints
  (("Goal"
    :use ((:instance zsp-patch-rope-output-summary-refines-zvr)
          (:instance zvr-patch-output-bi-summary-refines-output
                     (source (xef-rope-flatten source-rope)))
          (:instance xef-rope-summary-refines-flattening
                     (rope (zsp-patch-rope-output patch source-rope))))
    :in-theory
    (disable zsp-patch-rope-output-summary-refines-zvr
             zvr-patch-output-bi-summary-refines-output
             xef-rope-summary-refines-flattening))))

(defthm zsp-patch-rope-summary-correct
  (equal (zsp-patch-rope-summary patch source-rope table)
         (xef-rope-summary
          (zsp-patch-rope patch source-rope)
          table))
  :hints
  (("Goal"
    :cases ((zsp-patch-rope-okp patch source-rope))
    :in-theory
    (enable zsp-patch-rope-summary
            zsp-patch-rope))))

(defthm zsp-patch-rope-summary-refines-word
  (equal (zsp-patch-rope-summary patch source-rope table)
         (zvr-patch-word-bi-summary
          patch
          (xef-rope-flatten source-rope)
          table))
  :hints
  (("Goal"
    :use ((:instance zsp-patch-rope-summary-correct)
          (:instance xef-rope-summary-refines-flattening
                     (rope (zsp-patch-rope patch source-rope)))
          (:instance zvr-patch-word-bi-summary-refines-word
                     (source (xef-rope-flatten source-rope))))
    :in-theory
    (disable zsp-patch-rope-summary-correct
             xef-rope-summary-refines-flattening
             zvr-patch-word-bi-summary-refines-word))))

(defthm zsp-patch-rope-summary-of-normalize
  (equal (zsp-patch-rope-summary
          (zyp-normalize patch)
          source-rope
          table)
         (zsp-patch-rope-summary patch source-rope table))
  :hints
  (("Goal"
    :use ((:instance zsp-patch-rope-summary-refines-word
                     (patch (zyp-normalize patch)))
          (:instance zsp-patch-rope-summary-refines-word
                     (patch patch)))
    :in-theory
    (disable zsp-patch-rope-summary-refines-word))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Ground check
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zsp-demo-rope*
  (xef-rope-cat
   (xef-rope-cat
    (xef-rope-leaf '(a b))
    (xef-rope-leaf '(c d)))
   (xef-rope-cat
    (xef-rope-leaf '(e f))
    (xef-rope-leaf '(g h)))))

(defconst *zsp-demo-patch*
  (list (zyp-keep 3)
        (zyp-drop 2)
        (zyp-insert (xef-rle-encode '(x x y)))
        (zyp-keep 1)))

(assert-event
 (equal (xef-rope-flatten
         (zsp-patch-rope *zsp-demo-patch* *zsp-demo-rope*))
        '(a b c x x y f g h)))

(defxdoc zsp-user-interface
  :parents (zts-structural-rope-patch)
  :short "The structural transactional patch interface."
  :long
  "<p><tt>ZSP-PATCH-ROPE</tt> executes a patch without flattening its source.
  <tt>ZSP-PATCH-ROPE-SUMMARY</tt> computes the resulting bidirectional cocycle
  summary without flattening the source and without decoding inserted RLE
  runs.  Their correctness is stated extensionally by
  <tt>ZSP-FLATTEN-OF-PATCH-ROPE</tt> and
  <tt>ZSP-PATCH-ROPE-SUMMARY-CORRECT</tt>.</p>")
