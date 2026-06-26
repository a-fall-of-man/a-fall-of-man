; zpq-independent-action-calculus.lisp
;
; Guarded ordered-map actions, independence, and semantics-preserving
; canonical scheduling.

(in-package "ACL2")

(include-book "std/omaps/update" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zpq-independent-action-calculus
  :parents (acl2::top)
  :short "A certified calculus of guarded, commuting finite-map actions."
  :long
  "<p>An action has a tag, an ordered map of expected reads, and an ordered
  map of writes.  It commits exactly when every expected read agrees with the
  current ordered-map store.  Two actions are independent when neither writes
  a key read or written by the other.</p>

  <p>The central theorem proves that independent guarded actions commute,
  including all combinations of successful and rejected actions.  A second
  layer canonically sorts pairwise-independent traces by action tag and proves
  that scheduling does not change the resulting store.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Guarded actions over canonical ordered maps
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun via-action-tag (action)
  (car action))

(defun via-action-reads (action)
  (cadr action))

(defun via-action-writes (action)
  (caddr action))

(defun via-make-action (tag reads writes)
  (list tag (omap::mfix reads) (omap::mfix writes)))

(defun via-enabledp (action store)
  (omap::submap (via-action-reads action) store))

(defun via-apply-writes (writes store)
  (omap::update* writes store))

(defun via-run-action (action store)
  (if (via-enabledp action store)
      (via-apply-writes (via-action-writes action) store)
    (omap::mfix store)))

(defun via-disjoint-mapsp (left right)
  (if (omap::emptyp left)
      t
    (and (not (omap::assoc (omap::head-key left) right))
         (via-disjoint-mapsp (omap::tail left) right))))

(defun via-independentp (left right)
  (let ((lw (via-action-writes left))
        (lr (via-action-reads left))
        (rw (via-action-writes right))
        (rr (via-action-reads right)))
    (and (via-disjoint-mapsp lw rw)
         (via-disjoint-mapsp rw lw)
         (via-disjoint-mapsp lw rr)
         (via-disjoint-mapsp rr lw)
         (via-disjoint-mapsp rw lr)
         (via-disjoint-mapsp lr rw))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Ordered-map algebra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm via-disjoint-mapsp-of-tail-left
  (implies (via-disjoint-mapsp left right)
           (via-disjoint-mapsp (omap::tail left) right))
  :hints (("Goal" :in-theory (enable via-disjoint-mapsp))))

(defthm via-disjoint-mapsp-head-not-assoc
  (implies (and (via-disjoint-mapsp left right)
                (not (omap::emptyp left)))
           (not (omap::assoc (omap::head-key left) right)))
  :hints (("Goal" :in-theory (enable via-disjoint-mapsp))))

(defthm via-disjoint-mapsp-implies-compatiblep
  (implies (via-disjoint-mapsp left right)
           (omap::compatiblep left right))
  :hints
  (("Goal"
    :induct (via-disjoint-mapsp left right)
    :in-theory (enable via-disjoint-mapsp omap::compatiblep))))

(defthm via-disjoint-mapsp-excludes-assoc
  (implies (and (via-disjoint-mapsp reads writes)
                (omap::assoc key reads))
           (not (omap::assoc key writes)))
  :hints
  (("Goal"
    :induct (via-disjoint-mapsp reads writes)
    :in-theory
    (enable via-disjoint-mapsp
            omap::assoc-of-tail-when-not-head))))

(defthm via-assoc-of-update-star-when-disjoint
  (implies (and (via-disjoint-mapsp reads writes)
                (omap::assoc key reads))
           (equal (omap::assoc key (omap::update* writes store))
                  (omap::assoc key store)))
  :hints
  (("Goal"
    :use ((:instance omap::assoc-of-update*
                     (key key)
                     (map1 writes)
                     (map2 store))
          (:instance via-disjoint-mapsp-excludes-assoc
                     (reads reads)
                     (writes writes)
                     (key key)))
    :in-theory
    (disable omap::assoc-of-update*
             via-disjoint-mapsp-excludes-assoc))))

(defthm via-enabledp-preserved-by-disjoint-writes-aux
  (implies (via-disjoint-mapsp reads writes)
           (equal (omap::submap reads (omap::update* writes store))
                  (omap::submap reads store)))
  :hints
  (("Goal"
    :induct (omap::submap reads store)
    :in-theory (enable omap::submap via-disjoint-mapsp))))

(defthm via-apply-writes-commute
  (implies (and (via-disjoint-mapsp left right)
                (via-disjoint-mapsp right left))
           (equal (via-apply-writes left
                                    (via-apply-writes right store))
                  (via-apply-writes right
                                    (via-apply-writes left store))))
  :hints
  (("Goal"
    :use ((:instance via-disjoint-mapsp-implies-compatiblep
                     (left left) (right right))
          (:instance omap::commutativity-2-of-update*-when-compatiblep
                     (x left) (y right) (z store)))
    :in-theory (enable via-apply-writes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Independence laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm via-independentp-symmetric
  (equal (via-independentp left right)
         (via-independentp right left))
  :hints (("Goal" :in-theory (enable via-independentp))))

(defthm via-enabledp-preserved-by-independent-left
  (implies (via-independentp left right)
           (equal (via-enabledp right
                                (via-apply-writes
                                 (via-action-writes left)
                                 store))
                  (via-enabledp right store)))
  :hints
  (("Goal"
    :use ((:instance via-enabledp-preserved-by-disjoint-writes-aux
                     (writes (via-action-writes left))
                     (reads (via-action-reads right))))
    :in-theory (enable via-independentp via-enabledp))))

(defthm via-enabledp-preserved-by-independent-right
  (implies (via-independentp left right)
           (equal (via-enabledp left
                                (via-apply-writes
                                 (via-action-writes right)
                                 store))
                  (via-enabledp left store)))
  :hints
  (("Goal"
    :use ((:instance via-enabledp-preserved-by-independent-left
                     (left right) (right left)))
    :in-theory (disable via-enabledp-preserved-by-independent-left))))

(defthm via-independent-actions-commute
  (implies (via-independentp left right)
           (equal (via-run-action right
                                  (via-run-action left store))
                  (via-run-action left
                                  (via-run-action right store))))
  :hints
  (("Goal"
    :cases ((via-enabledp left store)
            (via-enabledp right store))
    :use ((:instance via-enabledp-preserved-by-independent-left)
          (:instance via-enabledp-preserved-by-independent-right)
          (:instance via-apply-writes-commute
                     (left (via-action-writes left))
                     (right (via-action-writes right))))
    :in-theory (enable via-run-action via-independentp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Trace execution and canonical scheduling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun via-run-trace (trace store)
  (if (endp trace)
      (omap::mfix store)
    (via-run-trace (cdr trace)
                   (via-run-action (car trace) store))))

(defun via-independent-of-listp (action trace)
  (if (endp trace)
      t
    (and (via-independentp action (car trace))
         (via-independent-of-listp action (cdr trace)))))

(defun via-pairwise-independentp (trace)
  (if (endp trace)
      t
    (and (via-independent-of-listp (car trace) (cdr trace))
         (via-pairwise-independentp (cdr trace)))))

(defun via-tag-before-p (left right)
  (<< (via-action-tag left)
      (via-action-tag right)))

(defun via-insert-action (action trace)
  (if (endp trace)
      (list action)
    (if (via-tag-before-p action (car trace))
        (cons action trace)
      (cons (car trace)
            (via-insert-action action (cdr trace))))))

(defun via-canonical-schedule (trace)
  (if (endp trace)
      nil
    (via-insert-action (car trace)
                       (via-canonical-schedule (cdr trace)))))

(defun via-tag-sortedp (trace)
  (or (endp trace)
      (endp (cdr trace))
      (and (not (via-tag-before-p (cadr trace) (car trace)))
           (via-tag-sortedp (cdr trace)))))

(defun via-insert-run-induction (action trace store)
  (if (endp trace)
      store
    (if (via-tag-before-p action (car trace))
        store
      (via-insert-run-induction
       action
       (cdr trace)
       (via-run-action (car trace) store)))))

(defthm via-run-trace-of-insert-action
  (implies (via-independent-of-listp action trace)
           (equal (via-run-trace (via-insert-action action trace) store)
                  (via-run-trace trace
                                 (via-run-action action store))))
  :hints
  (("Goal"
    :induct (via-insert-run-induction action trace store)
    :in-theory (enable via-insert-run-induction
                       via-insert-action
                       via-independent-of-listp
                       via-run-trace))))

(defthm via-independent-of-listp-of-insert
  (implies (and (via-independentp action inserted)
                (via-independent-of-listp action trace))
           (via-independent-of-listp
            action
            (via-insert-action inserted trace)))
  :hints
  (("Goal"
    :induct (via-insert-action inserted trace)
    :in-theory (enable via-insert-action
                       via-independent-of-listp))))

(defthm via-independent-of-listp-of-canonical-schedule
  (implies (via-independent-of-listp action trace)
           (via-independent-of-listp
            action
            (via-canonical-schedule trace)))
  :hints
  (("Goal"
    :induct (via-canonical-schedule trace)
    :in-theory (enable via-canonical-schedule
                       via-independent-of-listp))))

(defthm via-pairwise-independentp-of-insert
  (implies (and (via-pairwise-independentp trace)
                (via-independent-of-listp action trace))
           (via-pairwise-independentp
            (via-insert-action action trace)))
  :hints
  (("Goal"
    :induct (via-insert-action action trace)
    :in-theory (enable via-insert-action
                       via-pairwise-independentp
                       via-independent-of-listp))))

(defthm via-pairwise-independentp-of-canonical-schedule
  (implies (via-pairwise-independentp trace)
           (via-pairwise-independentp
            (via-canonical-schedule trace)))
  :hints
  (("Goal"
    :induct (via-canonical-schedule trace)
    :in-theory (enable via-canonical-schedule
                       via-pairwise-independentp))))

(defun via-schedule-run-induction (trace store)
  (if (endp trace)
      store
    (via-schedule-run-induction
     (cdr trace)
     (via-run-action (car trace) store))))

(defthm via-run-trace-of-canonical-schedule
  (implies (via-pairwise-independentp trace)
           (equal (via-run-trace (via-canonical-schedule trace) store)
                  (via-run-trace trace store)))
  :hints
  (("Goal"
    :induct (via-schedule-run-induction trace store)
    :in-theory (enable via-schedule-run-induction
                       via-canonical-schedule
                       via-pairwise-independentp))))

(defthm via-tag-sortedp-of-insert-action
  (implies (via-tag-sortedp trace)
           (via-tag-sortedp (via-insert-action action trace)))
  :hints
  (("Goal"
    :induct (via-insert-action action trace)
    :in-theory (enable via-insert-action
                       via-tag-sortedp
                       via-tag-before-p))))

(defthm via-tag-sortedp-of-canonical-schedule
  (via-tag-sortedp (via-canonical-schedule trace))
  :hints
  (("Goal"
    :induct (via-canonical-schedule trace)
    :in-theory (enable via-canonical-schedule))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Ground witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *via-store*
  (omap::update 'x 0 (omap::update 'z 0 nil)))

(defconst *via-action-a*
  (via-make-action
   'a
   (omap::update 'x 0 nil)
   (omap::update 'y 1 nil)))

(defconst *via-action-b*
  (via-make-action
   'b
   (omap::update 'z 0 nil)
   (omap::update 'w 2 nil)))

(assert-event
 (and (via-independentp *via-action-a* *via-action-b*)
      (equal (via-run-trace
              (list *via-action-a* *via-action-b*)
              *via-store*)
             (via-run-trace
              (list *via-action-b* *via-action-a*)
              *via-store*))))

(defxdoc via-user-interface
  :parents (zpq-independent-action-calculus)
  :short "Public interface for independent guarded actions."
  :long
  "<p>The executable interface is <tt>VIA-MAKE-ACTION</tt>,
  <tt>VIA-RUN-ACTION</tt>, <tt>VIA-INDEPENDENTP</tt>,
  <tt>VIA-RUN-TRACE</tt>, and <tt>VIA-CANONICAL-SCHEDULE</tt>.  The principal
  laws are <tt>VIA-INDEPENDENT-ACTIONS-COMMUTE</tt> and
  <tt>VIA-RUN-TRACE-OF-CANONICAL-SCHEDULE</tt>.</p>")
