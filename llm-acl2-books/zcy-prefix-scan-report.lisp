; zcy-prefix-scan-report.lisp
; Exact prefix scans, nonnegativity, and an FMT1 report writer.

(in-package "ACL2")

(defun vpb-sum (deltas)
  (if (endp deltas)
      0
    (+ (ifix (car deltas))
       (vpb-sum (cdr deltas)))))

(defun vpb-scan-from (deltas seed)
  (if (endp deltas)
      nil
    (let ((next (+ (ifix seed) (ifix (car deltas)))))
      (cons next
            (vpb-scan-from (cdr deltas) next)))))

(defun vpb-safe-fromp (deltas seed)
  (if (endp deltas)
      t
    (let ((next (+ (ifix seed) (ifix (car deltas)))))
      (and (<= 0 next)
           (vpb-safe-fromp (cdr deltas) next)))))

(defun vpb-all-nonnegativep (xs)
  (if (endp xs)
      t
    (and (<= 0 (ifix (car xs)))
         (vpb-all-nonnegativep (cdr xs)))))

(defthm vpb-sum-of-append
  (equal (vpb-sum (append left right))
         (+ (vpb-sum left) (vpb-sum right)))
  :hints (("Goal" :induct (len left)
           :in-theory (enable vpb-sum))))

(defthm vpb-scan-from-of-append
  (equal (vpb-scan-from (append left right) seed)
         (append (vpb-scan-from left seed)
                 (vpb-scan-from right
                                (+ (ifix seed)
                                   (vpb-sum left)))))
  :hints (("Goal" :induct (vpb-scan-from left seed)
           :in-theory (enable vpb-scan-from vpb-sum))))

(defthm vpb-safe-fromp-is-scan-nonnegative
  (equal (vpb-safe-fromp deltas seed)
         (vpb-all-nonnegativep
          (vpb-scan-from deltas seed)))
  :hints (("Goal" :induct (vpb-scan-from deltas seed)
           :in-theory (enable vpb-safe-fromp
                              vpb-all-nonnegativep
                              vpb-scan-from))))

(defun vpb-final-value (deltas seed)
  (+ (ifix seed) (vpb-sum deltas)))

(defthm vpb-final-value-of-append
  (equal (vpb-final-value (append left right) seed)
         (vpb-final-value
          right
          (vpb-final-value left seed)))
  :hints (("Goal" :in-theory (enable vpb-final-value))))

(defun vpb-write-rows (deltas index seed col channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (endp deltas)
      (mv col state)
    (let* ((delta (ifix (car deltas)))
           (next (+ (ifix seed) delta)))
      (mv-let (col state)
        (fmt1 "~c0~t1~c2~t3~c4~%"
              (list (cons #\0 (cons (nfix index) 8))
                    (cons #\1 12)
                    (cons #\2 (cons delta 12))
                    (cons #\3 28)
                    (cons #\4 (cons next 12)))
              col channel state nil)
        (vpb-write-rows (cdr deltas)
                        (1+ (nfix index))
                        next col channel state)))))

(defun vpb-write-report (filename deltas opening state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (not channel)
        (mv :open-failed state)
      (mv-let (col state)
        (fmt1 "Prefix scan report~%Initial: ~x0~%~%Index~t1Delta~t2Value~%"
              (list (cons #\0 (ifix opening))
                    (cons #\1 12)
                    (cons #\2 28))
              0 channel state nil)
        (mv-let (col state)
          (vpb-write-rows deltas 0 opening col channel state)
          (declare (ignore col))
          (mv-let (col state)
            (fmt1 "~%Final: ~x0; nonnegative throughout: ~x1.~%"
                  (list (cons #\0 (vpb-final-value deltas opening))
                        (cons #\1 (vpb-safe-fromp deltas opening)))
                  0 channel state nil)
            (declare (ignore col))
            (let ((state (close-output-channel channel state)))
              (mv nil state))))))))

(defconst *vpb-demo* '(7 -3 -4 6 -2))

(assert-event
 (and (equal (vpb-scan-from *vpb-demo* 2)
             '(9 6 2 8 6))
      (vpb-safe-fromp *vpb-demo* 2)
      (equal (vpb-final-value *vpb-demo* 2) 6)))
