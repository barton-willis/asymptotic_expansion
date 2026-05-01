(in-package :maxima)

(defun $myload (str)
  (load ($file_search str) :print t :verbose t))

(defvar *continuity-hashtable* (make-hash-table :size 32 :test #'eq))
(defvar *op* (make-hash-table))

(defun $report ()
  (maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *op*))

(defun continuous-p (e x pt)
  (let ((fn))
     (cond (($mapatom e) t)
     
           ((freeof x e) t)

           (($subvarp (mop e)) ;subscripted function
            (setq fn (gethash (subfunname e) *continuity-hashtable*))
            (if fn (funcall fn (subfunsubs e) (subfunargs e) x pt) nil))

           (t 
             (setq fn (gethash (caar e) *continuity-hashtable* nil))
			       (when (not fn)
			          (setf (gethash (caar e) *op*) (+ 1 (gethash (caar e) *op* 0))))
             (if fn (funcall fn (cdr e) x pt) nil)))))
          
(defun limit-by-continuity (e x pt)
  (cond (($mapatom e) (maxima-subst pt x e))
        ((continuous-p e x pt)
           (flet ((local-limit (q) ($limit q x pt)))
              (cond (($subvarp (op e))
                     (subfunmake 
		                     (subfunname e) 
                         (mapcar #'local-limit (subfunsubs e))
			                   (mapcar #'local-limit (subfunargs e))))
                  (t (fapply (caar e) (mapcar #'local-limit (cdr e)))))))))

(defun log-continuous-p (e x pt)
  (setq e (risplit (first e)))
  (and 
    (continuous-p (car e) x pt) 
    (continuous-p (cdr e) x pt)
    (eq t (mnqp 0 (maxima-substitute pt x (car e))))
    (eq t (mnqp 0 (maxima-substitute pt x (cdr e))))))
(setf (gethash '%log *continuity-hashtable*) #'log-continuous-p)
(setf (gethash '%expintegral_ei *continuity-hashtable*) #'log-continuous-p)

(defun gamma-continuous-p (e x pt)
    (setq e (first e))
    (cond ((continuous-p e x pt)
            (setq e (maxima-substitute pt x e))
            (not (and ($integerp e) (eq t (mgrp 0 e)))))
          (t nil)))
(setf (gethash '%gamma *continuity-hashtable*) #'gamma-continuous-p)

(defun mfactorial-continuous-p (e x pt)
    (setq e (first e))
    (cond ((continuous-p e x pt)
            (setq e (maxima-substitute pt x e))
            (not (and ($integerp e) (eq t (mgrp 1 e)))))
          (t nil)))
(setf (gethash 'mfactorial *continuity-hashtable*) #'mfactorial-continuous-p)

(defun expt-continuous-p (e x pt)
  (let ((a (first e)) (b (second e)))
    (cond ((and (continuous-p a x pt)
                (continuous-p b x pt))
            (setq a (maxima-substitute (ridofab pt) x a))
            (setq b (maxima-substitute (ridofab pt) x b))
            (or 
              (eq t (mgrp a 0))
              (and 
                 ($integerp b)
                 (eq t (mgrp b 0)))))
          (t nil))))
(setf (gethash 'mexpt *continuity-hashtable*) #'expt-continuous-p)

(defun floor-continuous-p (e x pt)
  (setq e (first e))
  (and  
    (continuous-p e x pt)
    ($featurep (maxima-substitute pt x e) '$noninteger)))
(setf (gethash '$floor *continuity-hashtable*) #'floor-continuous-p)
(setf (gethash '$ceiling *continuity-hashtable*) #'floor-continuous-p)

(defun round-continuous-p (e x pt)
  (setq e (first e))
  (and  
    (continuous-p e x pt)
    ($featurep (maxima-substitute pt x e) '$noninteger)))
;(setf (gethash '%round *continuity-hashtable*) #'floor-continuous-p)

(defun signum-continuous-p (e x pt)  
  (setq e (first e))
  (and 
      (continuous-p e x pt)
      (eq t (mnqp (maxima-substitute pt x e) 0))))
(setf (gethash '%signum *continuity-hashtable*) #'signum-continuous-p)      
(setf (gethash '$unit_step *continuity-hashtable*) #'signum-continuous-p)

(defun asinh-continuous-p (e x pt)
  (setq e (first e))
  (and 
      (continuous-p e x pt)
      ($featurep e '$real)))
(setf (gethash '%asinh *continuity-hashtable*) #'asinh-continuous-p)
(setf (gethash '%atan *continuity-hashtable*) #'asinh-continuous-p)

(defun atan2-continuous-p (e x pt)
  (let ((b (first e)) (a (second e)))
   (and 
      (continuous-p a x pt)
      (continuous-p b x pt)
      ($featurep a '$real)
      ($featurep b '$real)
      (eq t (mgrp (maxima-substitute pt x a) 0)))))
(setf (gethash '%atan2 *continuity-hashtable*) #'atan2-continuous-p)           

(setf (gethash '%asinh *continuity-hashtable*) #'asinh-continuous-p)
(setf (gethash '%atan *continuity-hashtable*) #'asinh-continuous-p)

(defun asin-continuous-p (e x pt)
  (setq e (first e))
  (and (continuous-p e x pt)
       (in-domain-of-asin (maxima-substitute pt x e))))
(setf (gethash '%asin *continuity-hashtable*) #'asin-continuous-p)
(setf (gethash '%acos *continuity-hashtable*) #'asin-continuous-p)
(setf (gethash '%atanh *continuity-hashtable*) #'asin-continuous-p)

(defun tan-continuous-p (e x pt)
    (setq e (first e))
    (and (continuous-p e x pt)
         (eq t (mnqp 0 (ftake '%cos (maxima-substitute pt x e))))))
(setf (gethash '%tan *continuity-hashtable*) #'tan-continuous-p)

(defun incomplete-gammma-continuous-p (e x pt)
    (let ((a (first e)) (z (second e)))
      (or (log-continuous-p e x pt)
          (and (integerp a) (> a 0)))))
(setf (gethash '%gamma_incomplete *continuity-hashtable*) #'incomplete-gammma-continuous-p)

(defun zeta-continuous-p (e x pt) 
   (setq e (first e))
   (and (continuous-p e x pt)
        (not (eql 1 (maxima-substitute pt x e)))
        (eq t (mnqp 1 (maxima-substitute pt x e)))))
(setf (gethash '%zeta *continuity-hashtable*) #'zeta-continuous-p)


(defmfun $continuous_p (e x pt)
   (continuous-p e x pt))

(defun default-continuous-p (e x pt)
   (every #'(lambda (q) (continuous-p q x pt)) e))

(dolist (xxx (list '%erf '%erfc '%integrate '$max '$min '%cos '%sin '%cosh '%sinh 'mplus 'mabs 
                   'mtimes '$conjugate '%imagpart '%realpart '%expintegral_ci))
    (setf (gethash xxx *continuity-hashtable*) #'default-continuous-p))             
