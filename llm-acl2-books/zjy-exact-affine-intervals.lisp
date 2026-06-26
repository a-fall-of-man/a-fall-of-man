; zjy-exact-affine-intervals.lisp
; Exact closed-interval semantics for integer affine transformers.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc zjy-exact-affine-intervals
  :parents (acl2::top)
  :short "Exact interval abstract interpretation for affine integer programs."
  :long "<p>Integer affine maps are interpreted both concretely and over closed
  integer intervals.  The interval transformer selects endpoints according to
  coefficient sign.  It is proved sound for every contained integer, and exact
  composition is proved: abstracting a composed affine map is identical to
  abstracting successively.</p>")

(fty::defprod vai-interval
  ((lo int)
   (hi int))
  :tag :vai-interval
  :layout :tree)

(fty::defprod vai-affine
  ((scale int)
   (offset int))
  :tag :vai-affine
  :layout :tree)

(defun vai-interval-okp (interval)
  (<= (vai-interval->lo interval)
      (vai-interval->hi interval)))

(defun vai-containsp (x interval)
  (and (integerp x)
       (<= (vai-interval->lo interval) x)
       (<= x (vai-interval->hi interval))))

(defun vai-apply (affine x)
  (+ (* (vai-affine->scale affine) (ifix x))
     (vai-affine->offset affine)))

(defun vai-compose (outer inner)
  (vai-affine (* (vai-affine->scale outer)
                 (vai-affine->scale inner))
              (+ (* (vai-affine->scale outer)
                    (vai-affine->offset inner))
                 (vai-affine->offset outer))))

(defun vai-image (affine interval)
  (let ((a (vai-affine->scale affine))
        (b (vai-affine->offset affine))
        (lo (vai-interval->lo interval))
        (hi (vai-interval->hi interval)))
    (if (< a 0)
        (vai-interval (+ (* a hi) b)
                      (+ (* a lo) b))
      (vai-interval (+ (* a lo) b)
                    (+ (* a hi) b)))))

(defthm vai-apply-of-compose
  (equal (vai-apply (vai-compose outer inner) x)
         (vai-apply outer (vai-apply inner x)))
  :hints (("Goal" :in-theory (enable vai-apply vai-compose))))

(defthm vai-image-is-well-formed
  (implies (vai-interval-okp interval)
           (vai-interval-okp (vai-image affine interval)))
  :hints (("Goal"
           :cases ((< (vai-affine->scale affine) 0))
           :in-theory (enable vai-image vai-interval-okp))))

(defthm vai-image-sound
  (implies (vai-containsp x interval)
           (vai-containsp (vai-apply affine x)
                          (vai-image affine interval)))
  :hints (("Goal"
           :cases ((< (vai-affine->scale affine) 0))
           :in-theory (enable vai-containsp vai-apply vai-image))))

(defthm vai-image-of-compose
  (equal (vai-image (vai-compose outer inner) interval)
         (vai-image outer (vai-image inner interval)))
  :hints (("Goal"
           :cases ((< (vai-affine->scale inner) 0)
                   (< (vai-affine->scale outer) 0)
                   (< (* (vai-affine->scale outer)
                         (vai-affine->scale inner))
                      0))
           :in-theory (enable vai-image vai-compose))))

(defun vai-run (program x)
  (if (endp program)
      (ifix x)
    (vai-run (cdr program)
             (vai-apply (car program) x))))

(defun vai-analyze (program interval)
  (if (endp program)
      (vai-interval-fix interval)
    (vai-analyze (cdr program)
                 (vai-image (car program) interval))))

(defun vai-analysis-induction (program x interval)
  (if (endp program)
      (list x interval)
    (vai-analysis-induction
     (cdr program)
     (vai-apply (car program) x)
     (vai-image (car program) interval))))

(defthm vai-analysis-sound
  (implies (vai-containsp x interval)
           (vai-containsp (vai-run program x)
                          (vai-analyze program interval)))
  :hints (("Goal"
           :induct (vai-analysis-induction program x interval)
           :in-theory (enable vai-analysis-induction vai-run vai-analyze))
          ("Subgoal *1/2"
           :use ((:instance vai-image-sound
                            (affine (car program))))
           :in-theory (disable vai-image-sound))))

(defthm vai-analyze-of-append
  (equal (vai-analyze (append first second) interval)
         (vai-analyze second (vai-analyze first interval)))
  :hints (("Goal"
           :induct (vai-analyze first interval)
           :in-theory (enable vai-analyze))))

(defconst *vai-demo-program*
  (list (vai-affine -2 7)
        (vai-affine 3 -1)))

(assert-event
 (equal (vai-analyze *vai-demo-program* (vai-interval 1 4))
        (vai-interval -4 14)))

(defxdoc vai-user-interface
  :parents (zjy-exact-affine-intervals)
  :short "Public interface for exact affine interval analysis."
  :long "<p><tt>VAI-IMAGE-SOUND</tt> is the concrete-to-abstract theorem;
  <tt>VAI-IMAGE-OF-COMPOSE</tt> proves exact compositionality; and
  <tt>VAI-ANALYSIS-SOUND</tt> lifts soundness to affine programs.</p>")
