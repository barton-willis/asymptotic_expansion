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

;; Taylor cannot handle conjugate expressions, so let's tell tlimit to 
;; not even try.
(defun tlimp (e)		
  (and (not (among '$conjugate e)) ($freeof '$ind e)))

;; The function conditional-radcan dispatches $radcan on every subexpression of 
;; the form (positive integer)^X. The function extra-mexpt-simp checks if the
;; input has the form (positive integer)^X and dispatches $radcan when it does.
(defun extra-mexpt-simp (e)
	(if (and (mexptp e) (integerp (cadr e)) (> (cadr e) 0)) 
		($radcan e) e))

(defun conditional-radcan (e)
	(scanmap1 #'extra-mexpt-simp e))

;; Dispatch Taylor, but recurse on the order until either the order 
;; reaches 16*lhospitallim or the Taylor polynomial is nonzero. When 
;; Taylor either fails to find a nonzero Taylor polynomial, return nil.

;; This recursion on the order attempts to handle limits such as 
;; tlimit(2^n/n^5, n, inf) correctly. 

;; We set up a reasonable environment for calling taylor. 

;; A user can set lhospitallim to a noninteger. That would make taylor
;; throw an error. So we set lhospitallim to 4 if it is noninteger. Also,
;; lhospitallim needs to be one or greater, so we enforce that too.

;; There is no good reason for defaulting the taylor order 
;; to lhospitallim, but it's in the user documentation. 

(defun tlimit-taylor (e x pt n)
	(let ((ee 0) 
	      ($lhospitallim (if (integerp $lhospitallim) (max 1 $lhospitallim) 4))
	      (silent-taylor-flag t) 
	      ($taylordepth 8)
		  ($taylor_logexpand nil)
		  ($maxtayorder t)
		  ($taylor_truncate_polynomials nil)
		  ($taylor_simplifier #'sratsimp))

        (setq e (conditional-radcan e))
        (setq ee ($ratdisrep (catch 'taylor-catch ($taylor e x pt n))))
		(cond ((and ee (not (alike1 ee 0))) 
		        ee)
              ((and ee (< n (* 16 $lhospitallim)))
			    (tlimit-taylor e x pt (* 2 (max 1 n))))
			  (t nil))))

(defun taylim (e x pt *i*)
	(let ((et nil) ($numer nil))
	  ;;(setq e (conditional-radcan e))
	  (when (or (eq pt '$inf) (eq pt '$minf))
	 	 (setq e (asymptotic-expansion e x pt $lhospitallim)))
	  (when (tlimp e) 
	     (setq et (errcatch (tlimit-taylor e x (ridofab pt) $lhospitallim)))
		 (setq et (car et)))

	  (cond (et 
	         (let ((taylored t))
			    (setq et (simplify ($ratdisrep et)))
				(limit et x pt 'think)))
			(t 
			  (let ((limit-using-taylor nil))
			  ;; I'm not sure about the logic behind choosing a limit method.
			  ;; Can we simply call limit? This logic was taken from Maxima's
			  ;; source code
			  (mtell "Taylor failed on ~M ~M ~M ~%" e x pt)
			  (cond ((eq *i* t)
			           (limit1 e x pt))
			        ((eq *i* 'think)
			          (if (member (caar e) '(mtimes mexpt) :test #'eq)
			              (limit1 e x pt)
			            (simplimit e x pt)))
			        (t
			              (simplimit e x pt))))))))

