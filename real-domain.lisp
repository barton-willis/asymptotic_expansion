(in-package :maxima)

;;; A hashtable for storing real-domain rules for functions.
(defvar *real-domain-hashtable* (make-hash-table :size 32 :test #'eq))

;;; User-level function that returns a Maxima list of inequalities that determine
;;; the real domain of the input `e'.
(defun $real_domain (e)
  "Return the real domain constraints for the expression 'e' as a Maxima list."
  (fapply 'mlist (real-domain e)))

(defun real-domain (e) 
  "Return the real domain constraints for the expression 'e' as a CL list."
  (let ((fn))
    (cond (($mapatom e) nil) ; If E is an atomic expression, return NIL.
          ((setq fn (gethash (caar e) *real-domain-hashtable* nil))
           (funcall fn (cdr e))) ; Call the associated real-domain function.
          (t (mapcan #'real-domain (cdr e)))))) ; Recurse for subexpressions.

;;; Function to compute real domain constraints for exponentiation expressions.
(defun mexpt-real-domain (e)
  "Computes the real domain constraints for the exponentiation expression E.
  Ensures constraints such as nonzero base for negative or zero exponents
  and positive base for fractional exponents with even denominators."
  (let ((x (first e)) (y (second e)) (fcts))
    (setq fcts (append (real-domain x) (real-domain y)))
    (cond ((and (integerp y) (<= y 0))
           (push (ftake '$notequal x 0) fcts)) ; Ensure base is nonzero.
          ((and ($ratnump y) ($evenp ($denom y)))
           (push (ftake 'mgreaterp x 0) fcts))) ; Ensure base is positive.
    fcts))
(setf (gethash 'mexpt *real-domain-hashtable*) #'mexpt-real-domain)

;;; Function to compute real domain constraints for logarithmic expressions.
(defun log-real-domain (e)
  "Return a CL list of the real domain constraints for `log(e)`"
  (list (ftake 'mgreaterp (first e) 0)))
(setf (gethash '%log *real-domain-hashtable*) #'log-real-domain)

;;; Function to compute real domain constraints for arcsine expressions.
(defun asin-real-domain (e)
  "Return a CL list of the real domain constraints for `asin(e)`"
  (let ((z (ftake '%asin (first e))))
    (list (ftake 'mgreaterp (first e) -1)  ; argument > -1.
          (ftake 'mgreaterp 1 (first e))  ; argument < 1.
          (ftake 'mgreaterp z 0)          ; arcsine result > 0.
          (ftake 'mgreaterp (div '$%pi 2) z)))) ; arcsine result < π/2.
(setf (gethash '%asin *real-domain-hashtable*) #'asin-real-domain)

;;; Function to compute real domain constraints for arccosine expressions.
(defun acos-real-domain (e)
  "Return a CL list of the real domain constraints for `asin(e)`"
  (list (ftake 'mgreaterp (first e) -1) ; argument > -1.
        (ftake 'mgreaterp 1 (first e)))) ; argument < 1.
(setf (gethash '%acos *real-domain-hashtable*) #'acos-real-domain)

