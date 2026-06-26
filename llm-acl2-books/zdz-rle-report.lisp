; zdz-rle-report.lisp
; Canonical RLE, exact decoding, and an FMT1 report writer.

(in-package "ACL2")

(defun vrf-run-length (x xs)
  (if (and (consp xs) (equal x (car xs)))
      (1+ (vrf-run-length x (cdr xs)))
    0))

(defun vrf-drop-run (x xs)
  (if (and (consp xs) (equal x (car xs)))
      (vrf-drop-run x (cdr xs))
    xs))

(defun vrf-repeat (n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons x (vrf-repeat (1- n) x))))

(defun vrf-encode (xs)
  (if (endp xs) nil
    (let ((x (car xs)))
      (cons (cons x (vrf-run-length x xs))
            (vrf-encode (vrf-drop-run x xs))))))

(defun vrf-decode (runs)
  (if (endp runs) nil
    (append (vrf-repeat (cdar runs) (caar runs))
            (vrf-decode (cdr runs)))))

(defun vrf-run-count-sum (runs)
  (if (endp runs) 0
    (+ (nfix (cdar runs))
       (vrf-run-count-sum (cdr runs)))))

(defthm vrf-run-length-positive
  (implies (consp xs)
           (< 0 (vrf-run-length (car xs) xs)))
  :hints (("Goal" :in-theory (enable vrf-run-length))))

(defthm true-listp-of-vrf-drop-run
  (implies (true-listp xs)
           (true-listp (vrf-drop-run x xs)))
  :hints (("Goal" :induct (vrf-drop-run x xs)
           :in-theory (enable vrf-drop-run))))

(defthm vrf-repeat-run-length-append-drop
  (implies (true-listp xs)
           (equal (append (vrf-repeat (vrf-run-length x xs) x)
                          (vrf-drop-run x xs))
                  xs))
  :hints (("Goal" :induct (vrf-run-length x xs)
           :in-theory (enable vrf-run-length vrf-drop-run vrf-repeat))))

(defthm vrf-decode-of-encode
  (implies (true-listp xs)
           (equal (vrf-decode (vrf-encode xs)) xs))
  :hints (("Goal" :induct (vrf-encode xs)
           :in-theory (enable vrf-encode vrf-decode))))

(defthm len-of-vrf-repeat
  (equal (len (vrf-repeat n x)) (nfix n))
  :hints (("Goal" :induct (vrf-repeat n x)
           :in-theory (enable vrf-repeat))))

(defthm len-of-vrf-decode
  (equal (len (vrf-decode runs))
         (vrf-run-count-sum runs))
  :hints (("Goal" :induct (vrf-decode runs)
           :in-theory (enable vrf-decode vrf-run-count-sum))))

(defthm vrf-run-count-sum-of-encode
  (implies (true-listp xs)
           (equal (vrf-run-count-sum (vrf-encode xs))
                  (len xs)))
  :hints (("Goal"
           :use ((:instance len-of-vrf-decode
                            (runs (vrf-encode xs)))
                 (:instance vrf-decode-of-encode))
           :in-theory (disable len-of-vrf-decode
                               vrf-decode-of-encode))))

(defun vrf-write-runs (runs col channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (endp runs)
      (mv col state)
    (mv-let (col state)
      (fmt1 "~x0~t1~c2~%"
            (list (cons #\0 (caar runs))
                  (cons #\1 32)
                  (cons #\2 (cons (cdar runs) 10)))
            col channel state nil)
      (vrf-write-runs (cdr runs) col channel state))))

(defun vrf-write-report (filename xs state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (not channel)
        (mv :open-failed state)
      (let ((runs (vrf-encode xs)))
        (mv-let (col state)
          (fmt1 "RLE report: ~x0 source items, ~x1 runs.~%~%Value~t2Count~%"
                (list (cons #\0 (len xs))
                      (cons #\1 (len runs))
                      (cons #\2 32))
                0 channel state nil)
          (mv-let (col state)
            (vrf-write-runs runs col channel state)
            (declare (ignore col))
            (let ((state (close-output-channel channel state)))
              (mv nil state))))))))

(defconst *vrf-demo* '(a a a b c c a a))

(assert-event
 (and (equal (vrf-encode *vrf-demo*)
             '((a . 3) (b . 1) (c . 2) (a . 2)))
      (equal (vrf-decode (vrf-encode *vrf-demo*))
             *vrf-demo*)))
