; znr-epochal-dependency-cache.lisp
;
; An abstract-stobj dependency cache whose logical content is an alist and
; whose executable content is a hash table.  Cached values carry snapshots of
; dependency revisions; revision bumps invalidate affected entries without a
; cache traversal.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/stobjs/def-hash" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(include-book "std/alists/hons-put-assoc" :dir :system)
(include-book "std/alists/hons-remove-assoc" :dir :system)
(include-book "std/omaps/update" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc znr-epochal-dependency-cache
  :parents (acl2::top)
  :short "A verified hash-backed cache with dependency-stamp invalidation."
  :long
  "<p>Each cached value stores the revisions of the symbolic dependencies from
  which it was computed.  A lookup is live exactly when all stored revisions
  still agree with the current revision map.  Bumping one dependency therefore
  invalidates every entry that mentioned it, without searching or mutating the
  cache; entries with disjoint dependency snapshots remain live.</p>

  <p>The cache is logically a duplicate-free alist and executably a Common Lisp
  hash table, via @(see stobjs::def-hash).  FTY supplies the entry and snapshot
  fixtypes.  Updater-independence theorems expose a compact frame interface for
  clients.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Typed entries and hash-backed abstract stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist vdc-stamp-alist
  :key-type symbol
  :val-type nat
  :true-listp t)

(fty::defprod vdc-entry
  ((value)
   (stamps vdc-stamp-alist))
  :tag :vdc-entry
  :layout :tree)

(fty::defalist vdc-entry-alist
  :key-type symbol
  :val-type vdc-entry
  :true-listp t)

(stobjs::def-hash vdc-cache
  :alistp vdc-entry-alist-p
  :key-p symbolp
  :key-fix symbol-fix
  :val-p vdc-entry-p
  :default-val (vdc-entry nil nil)
  :hash-test eq
  :parents (znr-epochal-dependency-cache))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Revision maps and snapshots
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vdc-revision (dependency revisions)
  (declare (xargs :guard (and (symbolp dependency)
                              (omap::mapp revisions))))
  (let ((look (omap::assoc (symbol-fix dependency) revisions)))
    (if look (nfix (cdr look)) 0)))

(defun vdc-bump (dependency revisions)
  (declare (xargs :guard (and (symbolp dependency)
                              (omap::mapp revisions))))
  (omap::update (symbol-fix dependency)
                (1+ (vdc-revision dependency revisions))
                revisions))

(defun vdc-capture (dependencies revisions)
  (declare (xargs :guard (and (symbol-listp dependencies)
                              (omap::mapp revisions))))
  (if (endp dependencies)
      nil
    (cons (cons (symbol-fix (car dependencies))
                (vdc-revision (car dependencies) revisions))
          (vdc-capture (cdr dependencies) revisions))))

(defun vdc-stamps-validp (stamps revisions)
  (declare (xargs :guard (and (vdc-stamp-alist-p stamps)
                              (omap::mapp revisions))))
  (if (endp stamps)
      t
    (and (equal (nfix (cdar stamps))
                (vdc-revision (caar stamps) revisions))
         (vdc-stamps-validp (cdr stamps) revisions))))

(defun vdc-entry-livep (entry revisions)
  (declare (xargs :guard (and (vdc-entry-p entry)
                              (omap::mapp revisions))))
  (and (vdc-entry-p entry)
       (vdc-stamps-validp (vdc-entry->stamps entry) revisions)))

(defthm vdc-revision-of-bump-same
  (equal (vdc-revision dependency
                       (vdc-bump dependency revisions))
         (1+ (vdc-revision dependency revisions)))
  :hints (("Goal" :in-theory (enable vdc-revision vdc-bump))))

(defthm vdc-revision-of-bump-different
  (implies (not (equal (symbol-fix dependency)
                       (symbol-fix other)))
           (equal (vdc-revision other
                                (vdc-bump dependency revisions))
                  (vdc-revision other revisions)))
  :hints (("Goal" :in-theory (enable vdc-revision vdc-bump))))

(defthm vdc-stamp-alist-p-of-capture
  (vdc-stamp-alist-p (vdc-capture dependencies revisions))
  :hints (("Goal"
           :induct (vdc-capture dependencies revisions)
           :in-theory (enable vdc-capture))))

(defthm strip-cars-of-vdc-capture
  (equal (strip-cars (vdc-capture dependencies revisions))
         (symbol-list-fix dependencies))
  :hints (("Goal"
           :induct (vdc-capture dependencies revisions)
           :in-theory (enable vdc-capture symbol-list-fix))))

(defthm vdc-capture-is-valid
  (vdc-stamps-validp (vdc-capture dependencies revisions)
                     revisions)
  :hints (("Goal"
           :induct (vdc-capture dependencies revisions)
           :in-theory (enable vdc-capture vdc-stamps-validp))))

(defthm vdc-validity-preserved-by-unmentioned-bump
  (implies (and (vdc-stamp-alist-p stamps)
                (vdc-stamps-validp stamps revisions)
                (not (member-equal (symbol-fix dependency)
                                   (strip-cars stamps))))
           (vdc-stamps-validp stamps
                              (vdc-bump dependency revisions)))
  :hints (("Goal"
           :induct (vdc-stamps-validp stamps revisions)
           :in-theory (enable vdc-stamps-validp))))

(defthm vdc-validity-destroyed-by-mentioned-bump
  (implies (and (vdc-stamp-alist-p stamps)
                (vdc-stamps-validp stamps revisions)
                (member-equal (symbol-fix dependency)
                              (strip-cars stamps)))
           (not (vdc-stamps-validp stamps
                                   (vdc-bump dependency revisions))))
  :hints (("Goal"
           :induct (vdc-stamps-validp stamps revisions)
           :in-theory (enable vdc-stamps-validp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Executable cache interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun vdc-install (key value dependencies revisions vdc-cache)
  (declare (xargs :stobjs vdc-cache
                  :guard (and (symbol-listp dependencies)
                              (omap::mapp revisions))))
  (vdc-cache-put
   (symbol-fix key)
   (vdc-entry value (vdc-capture dependencies revisions))
   vdc-cache))

(defun vdc-probe (key revisions vdc-cache)
  (declare (xargs :stobjs vdc-cache
                  :guard (omap::mapp revisions)))
  (if (vdc-cache-boundp (symbol-fix key) vdc-cache)
      (let ((entry (vdc-cache-get (symbol-fix key) vdc-cache)))
        (if (vdc-entry-livep entry revisions)
            (mv t (vdc-entry->value entry))
          (mv nil nil)))
    (mv nil nil)))

(defun vdc-forget (key vdc-cache)
  (declare (xargs :stobjs vdc-cache))
  (vdc-cache-rem (symbol-fix key) vdc-cache))

(defthm vdc-entry-livep-of-captured-entry
  (vdc-entry-livep
   (vdc-entry value (vdc-capture dependencies revisions))
   revisions)
  :hints (("Goal" :in-theory (enable vdc-entry-livep))))

(defthm vdc-probe-after-install
  (equal (vdc-probe key revisions
                    (vdc-install key value dependencies revisions vdc-cache))
         (mv t value))
  :hints (("Goal"
           :in-theory (enable vdc-probe vdc-install))))

(defthm vdc-probe-after-unrelated-install
  (implies (not (equal (symbol-fix key)
                       (symbol-fix other)))
           (equal (vdc-probe key revisions
                             (vdc-install other value dependencies revisions
                                          vdc-cache))
                  (vdc-probe key revisions vdc-cache)))
  :hints (("Goal"
           :in-theory (enable vdc-probe vdc-install))))

(defthm vdc-probe-after-unrelated-forget
  (implies (not (equal (symbol-fix key)
                       (symbol-fix other)))
           (equal (vdc-probe key revisions
                             (vdc-forget other vdc-cache))
                  (vdc-probe key revisions vdc-cache)))
  :hints (("Goal"
           :in-theory (enable vdc-probe vdc-forget))))

(defthm vdc-installed-entry-survives-unmentioned-bump
  (implies (not (member-equal (symbol-fix dependency)
                              (symbol-list-fix dependencies)))
           (equal
            (vdc-probe key
                       (vdc-bump dependency revisions)
                       (vdc-install key value dependencies revisions vdc-cache))
            (mv t value)))
  :hints
  (("Goal"
    :use ((:instance vdc-validity-preserved-by-unmentioned-bump
                     (stamps (vdc-capture dependencies revisions)))
          (:instance vdc-capture-is-valid)
          (:instance vdc-stamp-alist-p-of-capture)
          (:instance strip-cars-of-vdc-capture))
    :in-theory
    (e/d (vdc-probe vdc-install vdc-entry-livep)
         (vdc-bump
          vdc-capture
          vdc-stamps-validp
          vdc-validity-preserved-by-unmentioned-bump
          vdc-capture-is-valid
          strip-cars-of-vdc-capture)))))

(defthm vdc-installed-entry-dies-after-mentioned-bump
  (implies (member-equal (symbol-fix dependency)
                         (symbol-list-fix dependencies))
           (equal
            (vdc-probe key
                       (vdc-bump dependency revisions)
                       (vdc-install key value dependencies revisions vdc-cache))
            (mv nil nil)))
  :hints
  (("Goal"
    :use ((:instance vdc-validity-destroyed-by-mentioned-bump
                     (stamps (vdc-capture dependencies revisions)))
          (:instance vdc-capture-is-valid)
          (:instance vdc-stamp-alist-p-of-capture)
          (:instance strip-cars-of-vdc-capture))
    :in-theory
    (e/d (vdc-probe vdc-install vdc-entry-livep)
         (vdc-bump
          vdc-capture
          vdc-stamps-validp
          vdc-validity-destroyed-by-mentioned-bump
          vdc-capture-is-valid
          strip-cars-of-vdc-capture)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Frame interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(stobjs::def-updater-independence-thm vdc-probe-updater-independence
  (implies (and (equal (vdc-cache-boundp (symbol-fix key) new)
                       (vdc-cache-boundp (symbol-fix key) old))
                (equal (vdc-cache-get (symbol-fix key) new)
                       (vdc-cache-get (symbol-fix key) old)))
           (equal (vdc-probe key revisions new)
                  (vdc-probe key revisions old)))
  :hints (("Goal" :in-theory (enable vdc-probe))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Ground witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (let* ((revisions (omap::update 'source-a 3
                                 (omap::update 'source-b 7 nil)))
        (entry (vdc-entry 'compiled-object
                          (vdc-capture '(source-a source-b) revisions))))
   (and (vdc-entry-livep entry revisions)
        (not (vdc-entry-livep entry (vdc-bump 'source-a revisions)))
        (vdc-entry-livep entry (vdc-bump 'source-c revisions)))))

(defxdoc vdc-user-interface
  :parents (znr-epochal-dependency-cache)
  :short "Public interface for dependency-stamped memoization."
  :long
  "<p>Use <tt>VDC-INSTALL</tt>, <tt>VDC-PROBE</tt>, and <tt>VDC-FORGET</tt> on
  the <tt>VDC-CACHE</tt> abstract stobj.  Revision maps are immutable ordered
  maps manipulated by <tt>VDC-BUMP</tt>.  The central laws are
  <tt>VDC-INSTALLED-ENTRY-SURVIVES-UNMENTIONED-BUMP</tt> and
  <tt>VDC-INSTALLED-ENTRY-DIES-AFTER-MENTIONED-BUMP</tt>.</p>")
