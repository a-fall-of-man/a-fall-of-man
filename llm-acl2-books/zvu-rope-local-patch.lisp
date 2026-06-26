; zvu-rope-local-patch.lisp
;
; Transactional patching of a zipper focus in a binary rope, together with a
; bidirectional summary compiler that does not decode inserted RLE payloads.
;
; No SKIP-PROOFS, DEFAXIOM, trust tags, raw Lisp, program-mode definitions, or
; generated events are used.  ACL2 certification is the admission criterion.

(in-package "ACL2")

(include-book "zyl-verified-patch-calculus")

(defxdoc zvu-rope-local-patch
  :parents (zyl-verified-patch-calculus)
  :short "Transactional rope-local patches with certified incremental summaries."
  :long
  "<p>This book applies a verified patch to one focused rope subtree.  Success
  replaces the focused word by the patch output followed by its untouched
  suffix; failure is transactional and preserves the original word.  The
  surrounding zipper context is then rebuilt.</p>

  <p>A separate compiler computes the focused word's bidirectional cocycle
  summary.  Inserted run-length programs are summarized directly, without
  decoding them.  The principal theorem identifies the incremental result
  with the ordinary semantic summary of the rebuilt rope.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Bidirectional compilation of RLE words
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zvr-run-bi-summary (symbol count table)
  (let ((forward
         (xef-cocycle-power
          count
          (xef-lookup-cocycle symbol table))))
    (xef-bi-summary (nfix count) forward forward)))

(defun zvr-rle-bi-summary (runs table)
  (if (endp runs)
      (xef-bi-empty)
    (xef-bi-join
     (zvr-run-bi-summary (caar runs) (cdar runs) table)
     (zvr-rle-bi-summary (cdr runs) table))))

(defthm zvr-append-repeat-singleton
  (equal (append (xef-repeat n x) (list x))
         (cons x (xef-repeat n x)))
  :hints
  (("Goal"
    :use ((:instance xef-repeat-of-sum
                     (m n)
                     (n 1))
          (:instance xef-repeat-of-sum
                     (m 1)
                     (n n)))
    :in-theory (enable xef-repeat))))

(defthm zvr-rev-of-repeat
  (equal (xef-rev (xef-repeat n x))
         (xef-repeat n x))
  :hints
  (("Goal"
    :induct (xef-repeat n x)
    :in-theory (enable xef-repeat xef-rev))))

(defthm zvr-run-bi-summary-refines-repeat
  (equal (zvr-run-bi-summary symbol count table)
         (xef-word-bi-summary
          (xef-repeat count symbol)
          table))
  :hints
  (("Goal"
    :in-theory
    (enable zvr-run-bi-summary
            xef-word-bi-summary))))

(defthm zvr-rle-bi-summary-refines-decoding
  (equal (zvr-rle-bi-summary runs table)
         (xef-word-bi-summary
          (xef-rle-decode runs)
          table))
  :hints
  (("Goal"
    :induct (zvr-rle-bi-summary runs table))
   ("Subgoal *1/2"
    :expand ((zvr-rle-bi-summary runs table)
             (xef-rle-decode runs))
    :in-theory
    (e/d ()
         (zvr-run-bi-summary
          xef-word-bi-summary
          xef-bi-join
          xef-bi-summary
          xef-bi-empty
          xef-cocycle-compose
          xef-cocycle-fix)))
   ("Subgoal *1/1"
    :expand ((zvr-rle-bi-summary runs table)
             (xef-rle-decode runs))
    :in-theory
    (disable xef-word-bi-summary
             xef-bi-empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Bidirectional compilation of patch output
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zvr-step-output-bi-summary (instruction source table)
  (cond ((zyp-keep-p instruction)
         (xef-word-bi-summary
          (zyp-take (zyp-count instruction) source)
          table))
        ((zyp-insert-p instruction)
         (zvr-rle-bi-summary
          (zyp-insert-runs instruction)
          table))
        (t
         (xef-bi-empty))))

(defun zvr-patch-output-bi-summary (patch source table)
  (if (endp patch)
      (xef-bi-empty)
    (xef-bi-join
     (zvr-step-output-bi-summary (car patch) source table)
     (zvr-patch-output-bi-summary
      (cdr patch)
      (zyp-step-rest (car patch) source)
      table))))

(defthm zvr-step-output-bi-summary-refines-output
  (equal (zvr-step-output-bi-summary instruction source table)
         (xef-word-bi-summary
          (zyp-step-output instruction source)
          table))
  :hints
  (("Goal"
    :in-theory
    (enable zvr-step-output-bi-summary
            zyp-step-output))))

(defthm zvr-patch-output-bi-summary-refines-output
  (equal (zvr-patch-output-bi-summary patch source table)
         (xef-word-bi-summary
          (zyp-patch-output patch source)
          table))
  :hints
  (("Goal"
    :induct (zvr-patch-output-bi-summary patch source table))
   ("Subgoal *1/2"
    :expand ((zvr-patch-output-bi-summary patch source table)
             (zyp-patch-output patch source))
    :in-theory
    (e/d ()
         (zvr-step-output-bi-summary
          zyp-step-output
          zyp-step-rest
          xef-word-bi-summary
          xef-bi-join
          xef-bi-summary
          xef-bi-empty
          xef-cocycle-compose
          xef-cocycle-fix)))
   ("Subgoal *1/1"
    :expand ((zvr-patch-output-bi-summary patch source table)
             (zyp-patch-output patch source))
    :in-theory
    (disable xef-word-bi-summary
             xef-bi-empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Transactional word patches
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zvr-patch-word (patch source)
  (if (zyp-patch-okp patch source)
      (append (zyp-patch-output patch source)
              (zyp-patch-rest patch source))
    (true-list-fix source)))

(defun zvr-patch-word-bi-summary (patch source table)
  (if (zyp-patch-okp patch source)
      (xef-bi-join
       (zvr-patch-output-bi-summary patch source table)
       (xef-word-bi-summary
        (zyp-patch-rest patch source)
        table))
    (xef-word-bi-summary source table)))

(defthm zvr-word-summary-of-true-list-fix
  (equal (xef-word-summary (true-list-fix source) table)
         (xef-word-summary source table))
  :hints
  (("Goal"
    :induct (true-list-fix source)
    :in-theory
    (enable true-list-fix
            xef-word-summary))))

(defthm zvr-rev-of-true-list-fix
  (equal (xef-rev (true-list-fix source))
         (xef-rev source))
  :hints
  (("Goal"
    :induct (true-list-fix source)
    :in-theory
    (enable true-list-fix
            xef-rev))))

(defthm zvr-word-bi-summary-of-true-list-fix
  (equal (xef-word-bi-summary (true-list-fix source) table)
         (xef-word-bi-summary source table))
  :hints
  (("Goal"
    :in-theory
    (enable xef-word-bi-summary))))

(defthm zvr-true-listp-of-patch-word
  (true-listp (zvr-patch-word patch source))
  :hints
  (("Goal"
    :in-theory (enable zvr-patch-word))))

(defthm zvr-patch-word-bi-summary-refines-word
  (equal (zvr-patch-word-bi-summary patch source table)
         (xef-word-bi-summary
          (zvr-patch-word patch source)
          table))
  :hints
  (("Goal"
    :cases ((zyp-patch-okp patch source))
    :in-theory
    (enable zvr-patch-word-bi-summary
            zvr-patch-word))))

(defthm zvr-patch-word-of-normalize
  (equal (zvr-patch-word (zyp-normalize patch) source)
         (zvr-patch-word patch source))
  :hints
  (("Goal"
    :in-theory (enable zvr-patch-word))))

(defthm zvr-patch-word-bi-summary-of-normalize
  (equal (zvr-patch-word-bi-summary
          (zyp-normalize patch)
          source
          table)
         (zvr-patch-word-bi-summary patch source table))
  :hints
  (("Goal"
    :use ((:instance zvr-patch-word-bi-summary-refines-word
                     (patch (zyp-normalize patch)))
          (:instance zvr-patch-word-bi-summary-refines-word
                     (patch patch)))
    :in-theory (disable zvr-patch-word-bi-summary-refines-word))))

(defthm zvr-len-of-patch-word-when-okp
  (implies (zyp-patch-okp patch source)
           (equal (len (zvr-patch-word patch source))
                  (+ (zyp-output-length patch)
                     (- (len source)
                        (zyp-source-demand patch)))))
  :hints
  (("Goal"
    :in-theory (enable zvr-patch-word))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Rope-local execution and incremental summary replacement
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun zvr-edit-focus (patch focus context)
  (xef-plug-rope
   (xef-rope-leaf
    (zvr-patch-word patch (xef-rope-flatten focus)))
   context))

(defun zvr-edit-focus-summary (patch focus context table)
  (xef-plug-summary
   (zvr-patch-word-bi-summary
    patch
    (xef-rope-flatten focus)
    table)
   context
   table))

(defthm zvr-flatten-of-edit-focus
  (equal (xef-rope-flatten
          (zvr-edit-focus patch focus context))
         (xef-plug-word
          (zvr-patch-word patch (xef-rope-flatten focus))
          context))
  :hints
  (("Goal"
    :in-theory (enable zvr-edit-focus))))

(defthm zvr-edit-focus-summary-correct
  (equal (zvr-edit-focus-summary patch focus context table)
         (xef-rope-summary
          (zvr-edit-focus patch focus context)
          table))
  :hints
  (("Goal"
    :in-theory
    (enable zvr-edit-focus-summary
            zvr-edit-focus))))

(defthm zvr-flatten-of-failed-edit-focus
  (implies (not (zyp-patch-okp
                 patch
                 (xef-rope-flatten focus)))
           (equal (xef-rope-flatten
                   (zvr-edit-focus patch focus context))
                  (xef-rope-flatten
                   (xef-plug-rope focus context))))
  :hints
  (("Goal"
    :in-theory
    (enable zvr-edit-focus
            zvr-patch-word))))

(defthm zvr-edit-focus-summary-of-normalize
  (equal (zvr-edit-focus-summary
          (zyp-normalize patch)
          focus
          context
          table)
         (zvr-edit-focus-summary
          patch
          focus
          context
          table))
  :hints
  (("Goal"
    :in-theory (enable zvr-edit-focus-summary))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Ground checks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zvr-demo-focus*
  (xef-rope-cat
   (xef-rope-leaf '(a b c))
   (xef-rope-leaf '(d e f))))

(defconst *zvr-demo-context*
  (list (xef-left-frame (xef-rope-leaf '(g h)))))

(defconst *zvr-demo-patch*
  (list (zyp-keep 2)
        (zyp-drop 2)
        (zyp-insert (xef-rle-encode '(x x y)))))

(assert-event
 (equal (xef-rope-flatten
         (zvr-edit-focus
          *zvr-demo-patch*
          *zvr-demo-focus*
          *zvr-demo-context*))
        '(a b x x y e f g h)))

(defxdoc zvr-user-interface
  :parents (zvu-rope-local-patch)
  :short "The transactional local-edit and incremental-summary interface."
  :long
  "<p><tt>ZVR-EDIT-FOCUS</tt> applies a patch to the flattened focus subtree,
  replaces that subtree by one leaf, and plugs it through the zipper context.
  An undersupplied patch leaves the represented rope word unchanged.</p>

  <p><tt>ZVR-EDIT-FOCUS-SUMMARY</tt> computes the same rebuilt rope summary
  incrementally.  Its proof uses <tt>ZVR-RLE-BI-SUMMARY</tt>, which compiles RLE
  insertions directly and therefore does not allocate their decoded words.</p>")
