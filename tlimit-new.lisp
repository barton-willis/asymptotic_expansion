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

(declare-top (special taylored var val))

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
;; not even try. Also expressions that involve $ind sometimes get sign
;; called on them--that throws an error. So let's disallow expressions 
;; that involve $ind.
(defun tlimp (e)		
  (and (not (among '$conjugate e)) ($freeof '$ind e)))

;; Dispatch Taylor, but recurse on the order until either the order 
;; reaches 16*lhospitallim or the Taylor polynomial is nonzero. When 
;; Taylor either fails to find a nonzero Taylor polynomial, return nil.

;; This recursion on the order attempts to handle limits such as 
;; tlimit(2^n/n^5, n, inf) correctly.

;; We set up a reasonable environment taylor-this includes setting taylordepth,
;; and taylor_simplifier.

;; A user can set lhospitallim to a noninteger. That would make taylor
;; throw an error. So we set lhospitallim to 4 if it is noninteger. Also,
;; lhospitallim needs to be one or greater, so we enforce that too.

;; There is no good reason for defaulting the taylor order to lhospitallim, but 
;; it's documented. 

(defun tlimit-taylor (e x pt n)
	(let ((ee 0) 
	      ($lhospitallim (if (integerp $lhospitallim) (max 1 $lhospitallim) 4))
	      (silent-taylor-flag t) 
	      ($taylordepth 8)
		  ($taylor_logexpand nil)
		  ($maxtayorder t)
		  ($taylor_truncate_polynomials nil)
		  ($taylor_simplifier #'sratsimp))

        (setq ee ($totaldisrep (catch 'taylor-catch ($taylor e x pt n))))
		(cond ((and ee (not (alike1 ee 0))) 
		        ee)
              ((and ee (< n (* 16 $lhospitallim)))
			    (tlimit-taylor e x pt (* 2 (max 1 n))))
			  (t nil))))

(defun taylim (e x pt *i*)
	(let ((et nil))
	  ;(when (or (eq pt '$inf) (eq pt '$minf))
	  ;	 (setq e (asymptotic-expansion e x pt $lhospitallim)))
	  (when (tlimp e) 
	     (setq et (errcatch (tlimit-taylor e x (ridofab pt) $lhospitallim)))
		 (setq et (car et)))

      (mtell "et = ~M ~%" et)
	  (cond (et 
	            (let ((taylored t) (var x) (val pt))
				  (car (errcatch (limit et x pt *i*)))))
			(t 
			  ;; I'm not sure about the logic behind choosing a limit method.
			  ;; But this was taken from the current version of taylim

			;  (or (car (errcatch (simplimit e x pt)))
			;      (car (errcatch (limit1 e x pt))))))))

			  (cond ((eq *i* t)
			     (mtell "107: e = ~M var = ~M pt = ~M  ~%" e var pt)
			     (limit1 e x pt))
			  ((eq *i* 'think)
			      (let ((taylored t))
			      (mtell "108: e = ~M var = ~M pt = ~M path = ~M ~%" e var pt
				   (member (caar e) '(mtimes mexpt) :test #'eq))
			 	  (if (member (caar e) '(mtimes mexpt) :test #'eq)
			      (limit1 e x pt) (simplimit e x pt)))
			  (t
			   (mtell "109: e = ~M var = ~M pt = ~M  ~%" e var pt)
			   (simplimit e x pt)))))))
		    ;  (mtell "Taylor failed; e = ~M ; path = ~M ~% " e 
			 ;    (or (eq flag t) 
			 ;         (and (eq flag 'think) (or (mplusp e) (mtimesp e)))))

			;  (or (car (errcatch (simplimit e x pt)))
			;     (car (errcatch (limit1 e x pt)))
			 ; (limit1 e x pt)))))
			;  (if (or (eq flag t) 
			;          (and (eq flag 'think) (or (mplusp e) (mtimesp e))))
			;           (limit1 e x pt)
			;		   (simplimit e x pt))))))

