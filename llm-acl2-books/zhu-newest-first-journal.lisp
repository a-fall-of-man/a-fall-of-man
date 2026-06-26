; zhu-newest-first-journal.lisp
; Canonical compaction of newest-first key/value journals.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/omaps/update" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zhu-newest-first-journal
  :parents (acl2::top)
  :short "Certified compaction of newest-first event journals."
  :long "<p>A journal is ordered newest first.  Replay therefore processes the
  tail before applying the head.  Compaction retains only the first event for
  each key.  The principal theorem proves that compacted and original journals
  induce exactly the same canonical ordered-map store, for every initial
  store.  A second theorem proves that compacted journals have unique keys.</p>")

(fty::defprod vjl-event
  ((key symbol)
   (value))
  :tag :vjl-event
  :layout :tree)

(fty::deflist vjl-journal
  :elt-type vjl-event
  :true-listp t)

(defun vjl-apply-event (event store)
  (omap::update (vjl-event->key event)
                (vjl-event->value event)
                store))

(defun vjl-replay (journal store)
  (if (endp journal)
      (omap::mfix store)
    (vjl-apply-event
     (car journal)
     (vjl-replay (cdr journal) store))))

(defun vjl-key-memberp (key journal)
  (if (endp journal)
      nil
    (or (equal (symbol-fix key)
               (vjl-event->key (car journal)))
        (vjl-key-memberp key (cdr journal)))))

(defun vjl-remove-key (key journal)
  (if (endp journal)
      nil
    (if (equal (symbol-fix key)
               (vjl-event->key (car journal)))
        (vjl-remove-key key (cdr journal))
      (cons (car journal)
            (vjl-remove-key key (cdr journal))))))

(defun vjl-normalize (journal)
  (if (endp journal)
      nil
    (cons (car journal)
          (vjl-normalize
           (vjl-remove-key (vjl-event->key (car journal))
                           (cdr journal))))))

(defun vjl-unique-keysp (journal)
  (if (endp journal)
      t
    (and (not (vjl-key-memberp (vjl-event->key (car journal))
                               (cdr journal)))
         (vjl-unique-keysp (cdr journal)))))

(defthm vjl-key-memberp-of-remove-same
  (not (vjl-key-memberp key (vjl-remove-key key journal)))
  :hints (("Goal"
           :induct (vjl-remove-key key journal)
           :in-theory (enable vjl-remove-key vjl-key-memberp))))

(defthm vjl-key-memberp-of-remove-different
  (implies (not (equal (symbol-fix key)
                       (symbol-fix removed)))
           (equal (vjl-key-memberp key
                                   (vjl-remove-key removed journal))
                  (vjl-key-memberp key journal)))
  :hints (("Goal"
           :induct (vjl-remove-key removed journal)
           :in-theory (enable vjl-remove-key vjl-key-memberp))))

(defthm vjl-key-memberp-of-normalize
  (equal (vjl-key-memberp key (vjl-normalize journal))
         (vjl-key-memberp key journal))
  :hints (("Goal"
           :induct (vjl-normalize journal)
           :in-theory (enable vjl-normalize vjl-key-memberp))))

(defthm vjl-normalize-has-unique-keys
  (vjl-unique-keysp (vjl-normalize journal))
  :hints (("Goal"
           :induct (vjl-normalize journal)
           :in-theory (enable vjl-normalize vjl-unique-keysp))))

(defthm vjl-update-around-different-key
  (implies
   (and (not (equal key other))
        (equal (omap::update key value left)
               (omap::update key value right)))
   (equal
    (omap::update key value
                  (omap::update other other-value left))
    (omap::update key value
                  (omap::update other other-value right))))
  :hints
  (("Goal"
    :use ((:instance omap::update-different
                     (key1 key) (val1 value)
                     (key2 other) (val2 other-value)
                     (map left))
          (:instance omap::update-different
                     (key1 key) (val1 value)
                     (key2 other) (val2 other-value)
                     (map right)))
    :in-theory (disable omap::update-different)))
  :rule-classes nil)

(defthm vjl-replay-remove-key-under-update
  (equal
   (omap::update
    (symbol-fix key) value
    (vjl-replay (vjl-remove-key key journal) store))
   (omap::update
    (symbol-fix key) value
    (vjl-replay journal store)))
  :hints (("Goal"
           :induct (vjl-remove-key key journal)
           :in-theory (enable vjl-remove-key
                              vjl-replay
                              vjl-apply-event))
          ("Subgoal *1/3''"
           :use ((:instance vjl-update-around-different-key
                            (key (symbol-fix key))
                            (other (vjl-event->key (car journal)))
                            (other-value (vjl-event->value (car journal)))
                            (left (vjl-replay
                                   (vjl-remove-key key (cdr journal))
                                   store))
                            (right (vjl-replay (cdr journal) store)))))))

(defthm vjl-replay-of-normalize
  (equal (vjl-replay (vjl-normalize journal) store)
         (vjl-replay journal store))
  :hints (("Goal"
           :induct (vjl-normalize journal)
           :in-theory (enable vjl-normalize
                              vjl-replay
                              vjl-apply-event))
          ("Subgoal *1/2''"
           :use ((:instance vjl-replay-remove-key-under-update
                            (key (vjl-event->key (car journal)))
                            (value (vjl-event->value (car journal)))
                            (journal (cdr journal))))
           :in-theory (disable vjl-replay-remove-key-under-update))))

(defthm vjl-remove-key-when-absent
  (implies (not (vjl-key-memberp key journal))
           (equal (vjl-remove-key key journal)
                  (true-list-fix journal)))
  :hints (("Goal"
           :induct (vjl-remove-key key journal)
           :in-theory (enable vjl-remove-key vjl-key-memberp))))

(defthm vjl-normalize-when-unique
  (implies (and (true-listp journal)
                (vjl-unique-keysp journal))
           (equal (vjl-normalize journal)
                  journal))
  :hints (("Goal"
           :induct (len journal)
           :in-theory (enable vjl-normalize vjl-unique-keysp))))

(defthm vjl-normalize-idempotent
  (equal (vjl-normalize (vjl-normalize journal))
         (vjl-normalize journal))
  :hints (("Goal"
           :use ((:instance vjl-normalize-when-unique
                            (journal (vjl-normalize journal)))
                 (:instance vjl-normalize-has-unique-keys))
           :in-theory (disable vjl-normalize-when-unique
                               vjl-normalize-has-unique-keys))))

(defconst *vjl-demo*
  (list (vjl-event 'x 9)
        (vjl-event 'y 4)
        (vjl-event 'x 1)
        (vjl-event 'z 7)
        (vjl-event 'y 2)))

(assert-event
 (and (equal (len (vjl-normalize *vjl-demo*)) 3)
      (equal (omap::assoc 'x (vjl-replay *vjl-demo* nil))
             '(x . 9))
      (equal (vjl-replay (vjl-normalize *vjl-demo*) nil)
             (vjl-replay *vjl-demo* nil))))

(defxdoc vjl-user-interface
  :parents (zhu-newest-first-journal)
  :short "Public interface for journal compaction."
  :long "<p><tt>VJL-REPLAY</tt> interprets newest-first journals;
  <tt>VJL-NORMALIZE</tt> removes shadowed events;
  <tt>VJL-REPLAY-OF-NORMALIZE</tt> proves exact store preservation; and
  <tt>VJL-NORMALIZE-HAS-UNIQUE-KEYS</tt> proves canonical key uniqueness.</p>")
