;;; -*-  Mode: Lisp; Package: Maxima; Syntax: Common-Lisp; Base: 10 -*- ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     The data in this file contains enhancments.                    ;;;;;
;;;                                                                    ;;;;;
;;;  Copyright (c) 1984,1987 by William Schelter,University of Texas   ;;;;;
;;;     All rights reserved                                            ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     (c) Copyright 1980 Massachusetts Institute of Technology         ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :maxima)

(declare-top (special taylored))

(macsyma-module tlimit)

(load-macsyma-macros rzmac)

;; TOP LEVEL FUNCTION(S): $TLIMIT $TLDEFINT

(defmfun $tlimit (&rest args)
  (let ((limit-using-taylor t))
    (declare (special limit-using-taylor))
    (apply #'$limit args)))

(defmfun $tldefint (exp var ll ul)
  (let ((limit-using-taylor t))
    (declare (special limit-using-taylor))
    ($ldefint exp var ll ul)))

;; Taylor cannot handle conjugate, ceiling, floor, unit_step, or signum 
;; expressions, so let's tell tlimit to *not* try. We also disallow 
;; expressions containing $ind.

;; Likely, the simplimit%functions for floor, ceiling, unit_step, and signum
;; should call behavior--that might allow them to evaluate a few more limits.
(defun tlimp (e)		
  (not (amongl '($conjugate $floor $ceiling $ind $unit_step %signum) e)))

;; Dispatch Taylor, but recurse on the order until either the order 
;; reaches 16*lhospitallim or the Taylor polynomial is nonzero. When 
;; Taylor either fails to find a nonzero Taylor polynomial, return nil.

;; This recursion on the order attempts to handle limits such as 
;; tlimit(2^n/n^5, n, inf) correctly. 

;; We set up a reasonable environment for calling taylor. Arguably, setting
;; these option variables is overly removes the users ability to adjust these
;; option variables.

;; I know of no compelling reason for defaulting the taylor order to 
;; lhospitallim, but this is documented (user documentation). 
(defun tlimit-taylor (e x pt n)
	(let ((ee 0) 
	      (silent-taylor-flag t) 
	      ($taylordepth 8)
		  ($taylor_logexpand t)
		  ($taylor_simplifier #'extra-simp))
        (setq ee ($ratdisrep (catch 'taylor-catch ($taylor e x pt n))))
		(cond ((and ee (not (alike1 ee 0))) ee)
			  ;; When taylor returns zero and n is less than 16 x lhospitallim, 
			  ;; declare a do-over--otherwise return nil.
              ((and ee (< n (* 16 $lhospitallim)))
			    (tlimit-taylor e x pt (* 2 (max 1 n))))
			  (t nil))))

;; Previously when the taylor series failed, there was code for deciding
;; whether to call limit1 or simplimit. The choice depended on the last
;; argument to taylim (previously named *i*) and the main operator of the 
;; expression. This code dispenses with this logic and dispatches limit1.
;; this change orphans the last argument of taylim.

;; The call to stirling0 fixes the bug limit(gamma(x)/gamma(1/x),x,0,plus),
;; but it causes a bug integrate((log(1-x)*log(1+x))/(1+x),x,0,1) --> limit 
;; nounform.

(defvar *failed* nil)
(defun taylim (e x pt flag) 
	(let ((et nil))
	  (when (tlimp e)
	     (mtell "before:  ~M ~%" e) 
		 (setq e (stirling0 e))
		 (mtell "after:  ~M ~%" e) 
	     (setq et (tlimit-taylor e x (ridofab pt) $lhospitallim)))
	
	  (when (null et)
	  	(push (ftake 'mlist e x pt) *failed*))

	  (if et (let ((taylored t)) (limit et x pt flag)) (limit1 e x pt))))

