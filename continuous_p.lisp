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
          
(defun limit-by-direct-subst (e x pt)
  (if (continuous-p e x pt) (maxima-substitute pt x e) nil))

(defun log-continuous-p (e x pt)
  (setq e (risplit (first e)))
  (and 
    (continuous-p (car e) x pt) 
    (continuous-p (cdr e) x pt)
    (eq t (mnqp 0 (maxima-substitute pt x (car e))))
    (eq t (mnqp 0 (maxima-substitute pt x (cdr e))))))
(setf (gethash '%log *c-hashtable*) #'log-continuous-p)

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
;(setf (gethash 'mfactorial *c-hashtable*) #'mfactorial-continuous-p)

(defun expt-continuous-p (e x pt)
  (let ((a (first e)) (b (second e)))
    (cond ((and (continuous-p a x pt)
                (continuous-p b x pt))
            (setq a (maxima-substitute pt x a))
            (setq b (maxima-substitute pt x b))
            (or 
              (eq t (mgrp a 0))
              (and 
                 ($integerp b)
                 (eq t (mgrp b 0))))))))
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
    ($featurep (sub (maxima-substitute pt x e) (div 1 2))
      '$noninteger)))
(setf (gethash '%round *c-hashtable*) #'floor-continuous-p)

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
   (mtell "a = ~M; b = ~M; x = ~M ; pt = ~M ~%" a b x pt)
   (and 
      (continuous-p a x pt)
      (continuous-p b x pt)
      ($featurep a '$real)
      ($featurep b '$real)
      (eq t (mgrp (maxima-substitute pt x a) 0)))))
(setf (gethash '$atan2 *c-hashtable*) #'atan2-continuous-p)           

(setf (gethash '%asinh *c-hashtable*) #'asinh-continuous-p)
(setf (gethash '%atan *c-hashtable*) #'asinh-continuous-p)

(defmfun $continuous_p (e x pt)
   (continuous-p e x pt))

(defun default-continuous-p (e x pt)
   (every #'(lambda (q) (continuous-p q x pt)) e))

(dolist (xxx (list '%integrate '$max '$min '%cos '%sin '%cosh '%sinh 'mplus 'mabs 'mtimes '$conjugate))
    (setf (gethash xxx *c-hashtable*) #'default-continuous-p))             
