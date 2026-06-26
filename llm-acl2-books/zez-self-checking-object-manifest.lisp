; zez-self-checking-object-manifest.lisp
; Self-checking object manifests with ACL2 object-channel save/load routines.

(in-package "ACL2")

(defun vom-byte-listp (xs)
  (if (consp xs)
      (and (natp (car xs))
           (< (car xs) 256)
           (vom-byte-listp (cdr xs)))
    (equal xs nil)))

(defthm vom-byte-listp-implies-true-listp
  (implies (vom-byte-listp xs)
           (true-listp xs))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (len xs)
           :in-theory (enable vom-byte-listp))))

(defun vom-checksum (xs)
  (if (endp xs) 0
    (+ (nfix (car xs))
       (vom-checksum (cdr xs)))))

(defun vom-make (payload)
  (list :acl2-manifest
        (len payload)
        (mod (vom-checksum payload) 65536)
        payload))

(defun vom-validp (x)
  (and (true-listp x)
       (equal (len x) 4)
       (equal (nth 0 x) :acl2-manifest)
       (vom-byte-listp (nth 3 x))
       (equal (nth 1 x) (len (nth 3 x)))
       (equal (nth 2 x)
              (mod (vom-checksum (nth 3 x)) 65536))))

(defun vom-payload (x)
  (if (vom-validp x) (nth 3 x) nil))

(defthm vom-byte-listp-of-append
  (implies (true-listp a)
           (equal (vom-byte-listp (append a b))
                  (and (vom-byte-listp a)
                       (vom-byte-listp b))))
  :hints (("Goal" :induct (len a)
           :in-theory (enable vom-byte-listp))))

(defthm vom-checksum-of-append
  (equal (vom-checksum (append a b))
         (+ (vom-checksum a)
            (vom-checksum b)))
  :hints (("Goal" :induct (len a)
           :in-theory (enable vom-checksum))))

(defthm vom-validp-of-make
  (implies (vom-byte-listp payload)
           (vom-validp (vom-make payload)))
  :hints (("Goal" :in-theory (enable vom-validp vom-make))))

(defthm vom-payload-of-make
  (implies (vom-byte-listp payload)
           (equal (vom-payload (vom-make payload))
                  payload))
  :hints (("Goal" :in-theory (enable vom-payload))))

(defun vom-save (filename payload state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (channel state)
    (open-output-channel filename :object state)
    (if (not channel)
        (mv :open-failed state)
      (pprogn
       (print-object$ (vom-make payload) channel state)
       (close-output-channel channel state)
       (mv nil state)))))

(defun vom-load (filename state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        (mv :open-failed nil state)
      (mv-let (eofp object state)
        (read-object channel state)
        (let ((state (close-input-channel channel state)))
          (cond
           (eofp
            (mv-let (col state)
              (fmt "Manifest ~x0 was empty.~%"
                   (list (cons #\0 filename))
                   *standard-co* state nil)
              (declare (ignore col))
              (mv :empty nil state)))
           ((not (vom-validp object))
            (mv-let (col state)
              (fmt "Manifest ~x0 failed count or checksum validation.~%"
                   (list (cons #\0 filename))
                   *standard-co* state nil)
              (declare (ignore col))
              (mv :invalid nil state)))
           (t (mv nil (vom-payload object) state))))))))

(defconst *vom-demo* '(1 2 3 250 255))

(assert-event
 (and (vom-validp (vom-make *vom-demo*))
      (equal (vom-payload (vom-make *vom-demo*)) *vom-demo*)
      (equal (vom-checksum *vom-demo*) 511)))
