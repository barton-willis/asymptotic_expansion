(in-package :maxima)

(defun $myload (str)
  (load ($file_search str) :print t :verbose t))

(defvar *c-hashtable* (make-hash-table :size 32 :test #'eq))
(defvar *op* (make-hash-table))

(defun $report ()
  (maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *op*))

(defun continuous-p (e x pt)
  (let ((fn))
     (cond ((memq pt (list '$minf '$inf '$infinity '$und '$ind)) nil)
           ((memq e (list '$minf '$inf '$infinity '$und '$ind)) nil)
           (($mapatom e) t)
           (t 
             (setq fn (gethash (caar e) *c-hashtable* nil))
             (when (not fn)
                (setf (gethash (caar e) *op*) (+ 1 (gethash (caar e) *op* 0))))
             (if fn (funcall fn (cdr e) x pt) nil)))))
          

(defmfun $ds (e x pt)
  (let ((g (gensym)))
    (assume (ftake 'mgreaterp (div 1 1000000) g))
    (assume (ftake 'mgreaterp g (div -1 1000000)))
    (setq e (maxima-substitute (add pt g) x e))
    (mtell "e = ~M ~%" e)
    (limit-by-direct-subst e g '$zeroa)))

(defvar *ds* 0)
(defun limit-by-direct-subst (e x pt)
  (let ((ans))
  (cond ((and (eql (ridofab pt) 0) (continuous-p e x 0)) 
       (incf *ds* 1)
       (setq ans (maxima-substitute 0 x e))
       (if (eql ans 0)
          (zero-fixup e x pt)
          ans))
        (t nil))))

(defun log-continuous-p (e x pt)
  (setq e (risplit (first e)))
  (and 
    (continuous-p (car e) x pt) 
    (continuous-p (cdr e) x pt)
    (eq t (mnqp 0 (maxima-substitute pt x (car e))))
    (eq t (mnqp 0 (maxima-substitute pt x (cdr e))))))
(setf (gethash '%log *c-hashtable*) #'log-continuous-p)
(setf (gethash '%expintegral_ei *c-hashtable*) #'log-continuous-p)

(defun gamma-continuous-p (e x pt)
    (setq e (first e))
    (cond ((continuous-p e x pt)
            (setq e (maxima-substitute pt x e))
            (not (and ($integerp e) (eq t (mgrp 0 e)))))
          (t nil)))
(setf (gethash '%gamma *c-hashtable*) #'gamma-continuous-p)

(defun mfactorial-continuous-p (e x pt)
    (setq e (first e))
    (cond ((continuous-p e x pt)
            (setq e (maxima-substitute pt x e))
            (not (and ($integerp e) (eq t (mgrp 1 e)))))
          (t nil)))
(setf (gethash 'mfactorial *c-hashtable*) #'mfactorial-continuous-p)

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
(setf (gethash 'mexpt *c-hashtable*) #'expt-continuous-p)

(defun floor-continuous-p (e x pt)
  (setq e (first e))
  (and  
    (continuous-p e x pt)
    ($featurep (maxima-substitute pt x e) '$noninteger)))
(setf (gethash '$floor *c-hashtable*) #'floor-continuous-p)
(setf (gethash '$ceiling *c-hashtable*) #'floor-continuous-p)

(defun round-continuous-p (e x pt)
  (setq e (first e))
  (and  
    (continuous-p e x pt)
    ($featurep (maxima-substitute pt x e) '$noninteger)))
;(setf (gethash '%round *c-hashtable*) #'floor-continuous-p)

(defun signum-continuous-p (e x pt)  
  (setq e (first e))
  (and 
      (continuous-p e x pt)
      (eq t (mnqp (maxima-substitute pt x e) 0))))
(setf (gethash '%signum *c-hashtable*) #'signum-continuous-p)      
(setf (gethash '$unit_step *c-hashtable*) #'signum-continuous-p)

(defun asinh-continuous-p (e x pt)
  (setq e (first e))
  (and 
      (continuous-p e x pt)
      ($featurep e '$real)))
(setf (gethash '%asinh *c-hashtable*) #'asinh-continuous-p)
(setf (gethash '%atan *c-hashtable*) #'asinh-continuous-p)

(defun atan2-continuous-p (e x pt)
  (let ((b (first e)) (a (second e)))
   (and 
      (continuous-p a x pt)
      (continuous-p b x pt)
      ($featurep a '$real)
      ($featurep b '$real)
      (eq t (mgrp (maxima-substitute pt x a) 0)))))
(setf (gethash '%atan2 *c-hashtable*) #'atan2-continuous-p)           

(setf (gethash '%asinh *c-hashtable*) #'asinh-continuous-p)
(setf (gethash '%atan *c-hashtable*) #'asinh-continuous-p)

(defun asin-continuous-p (e x pt)
  (setq e (first e))
  (and (continuous-p e x pt)
       (in-domain-of-asin (maxima-substitute pt x e))))
(setf (gethash '%asin *c-hashtable*) #'asin-continuous-p)
(setf (gethash '%acos *c-hashtable*) #'asin-continuous-p)
(setf (gethash '%atanh *c-hashtable*) #'asin-continuous-p)

(defun tan-continuous-p (e x pt)
    (setq e (first e))
    (and (continuous-p e x pt)
         (eq t (mnqp 0 (ftake '%cos (maxima-substitute pt x e))))))
(setf (gethash '%tan *c-hashtable*) #'tan-continuous-p)

(defun incomplete-gammma-continuous-p (e x pt)
    (let ((a (first e)) (z (second e)))
      (or (log-continuous-p e x pt)
          (and (integerp a) (> a 0)))))
(setf (gethash '%gamma_incomplete *c-hashtable*) #'incomplete-gammma-continuous-p)

(defun zeta-continuous-p (e x pt) 
   (setq e (first e))
   (and (continuous-p e x pt)
        (not (eql 1 (maxima-substitute pt x e)))
        (eq t (mnqp 1 (maxima-substitute pt x e)))))
(setf (gethash '%zeta *c-hashtable*) #'zeta-continuous-p)


(defmfun $continuous_p (e x pt)
   (continuous-p e x pt))

(defun default-continuous-p (e x pt)
   (every #'(lambda (q) (continuous-p q x pt)) e))

(dolist (xxx (list '%erf '%erfc '%integrate '$max '$min '%cos '%sin '%cosh '%sinh 'mplus 'mabs 
                   'mtimes '$conjugate '%imagpart '%realpart '%expintegral_ci))
    (setf (gethash xxx *c-hashtable*) #'default-continuous-p))             
