#|
Error summary: Using the hacked approx-alike that uses an extra ratsimp--I think the share
tests that now pass are simply due to this extra ratsimp, not a real bug fix:
Error(s) found:
    rtest15.mac problem:    (425)
    rtestint.mac problem:    (241)
    rtest_limit.mac problems:    (178 179 232)
    rtest_limit_extra.mac problems:    (94 308 309 411)
    rtest_limit_gruntz.mac problem:    (27)
Tests that were expected to fail but passed:
    rtest_limit.mac problem:    (113)
    rtest_limit_extra.mac problems:    (268 269 270)
    rtest_limit_gruntz.mac problem:   (38)
10 tests failed out of 14,765 total tests.

Most wanted bug:

 limit(exp(x)*(gamma(x + exp(- x)) - gamma(x)), x, inf);
 |#

(in-package :maxima)

(declare-top (special origval
		      *indicator numer denom exp var val
		      taylored logcombed
		      $exponentialize lhp? lhcount
		      loginprod? context limit-assumptions
		      limit-top))

(defvar *debug-limit* nil)

;; Until simplimtimes runs the testsuite & share testsuites without failures and no
;; calls to asksign, let's dispatch both the old and new simplimtimes functions. When
;; the old and new disagree, save this data in list *times*.

;; Save original simplimtimes only once
(unless (fboundp 'old-simplimtimes)
  (setf (symbol-function 'old-simplimtimes)
        (symbol-function 'simplimtimes)))

(defvar *times* nil)

(defmfun $show_d ()
  (fapply 'mlist *times*))

(defmfun $reset_d ()
  (setq *times* nil))

(defun simplimtimes (e)
  (let ((old (old-simplimtimes e))
        (new (new-simplimtimes e)))
    (when (not (alike1 old new))
       (push (ftake 'mlist (fapply 'mtimes e) var val old new) *times*))
    new))

;; We use a hashtable to represent the multiplication table for extended
;; real numbers. The table is symmetric, so we list only its "upper" half.
;; When a value isn't found in the hashtable, mult-extended-real returns `$und`,
;; so we omit entries for those cases.

;; This multiplication is commutative and associative, but not distributive. For example, 
;; inf*(inf + zeroa) = inf, but inf * inf + inf * zeroa = und.
(defvar *extended-real-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mult-table*) (third a)))
   (list (list '$minf '$minf '$inf)
         (list '$minf '$inf '$minf)
         (list '$minf '$infinity '$infinity)

         (list '$zerob '$zerob '$zeroa)
         (list '$zerob '$zeroa '$zerob)
         (list '$zerob 0 0)

         (list '$zeroa '$zeroa '$zeroa)
         (list '$zeroa 0 0)
         (list 0 0 0)
         
         (list '$inf '$inf '$inf)
         (list '$inf '$infinity '$infinity)

         (list '$infinity '$infinity '$infinity)

         (list '$ind '$ind '$ind)))

(defun mul-extended-real (a b)
  "Multiply `a` and `b`, where each is either an extended real or one.
   If both are extended reals, look up their product in *extended-real-mult-table*.
   The table is symmetric: first try `(a,b)`, then `(b,a)`. If neither is found, return `$und`."
  (cond
    ((onep a) b)
    ((onep b) a)
    (t (or (gethash (list a b) *extended-real-mult-table*)
           (gethash (list b a) *extended-real-mult-table*)
           '$und))))

(defvar *extended-real-times-sign-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-times-sign-mult-table*) (third a)))
(list (list '$minf '$neg '$inf)
      (list '$minf '$pos '$minf)
	    (list '$minf '$imaginary '$infinity) ; not sure
	    (list '$minf '$complex '$infinity)   ;not sure

	    (list '$inf '$neg '$minf)
      (list '$inf '$pos '$inf)
	    (list '$inf '$imaginary '$infinity) ;not sure
	    (list '$inf '$complex '$infinity)   ;not sure

	    (list '$infinity '$neg '$infinity)
      (list '$infinity '$pos '$infinity)
	    (list '$infinity '$pn '$infinity) ;not sure
	    (list '$infinity '$imaginary '$infinity)
	    (list '$infinity '$complex '$infinity)

      ;; zerob x {neg, nz, zero, pz, pn, pos, pnz, imaginary, complex} is a zero
	    (list '$zerob '$pos '$zerob)
	    (list '$zerob '$neg '$zeroa)
	    (list '$zerob '$nz 0)
      (list '$zerob '$zero 0)
      (list '$zerob '$pz 0)
      (list '$zerob '$pn 0)
      (list '$zerob '$pnz 0)
      (list '$zerob '$imaginary 0)
      (list '$zerob '$complex 0)

      (list '$zeroa '$pos '$zeroa)
	    (list '$zeroa '$neg '$zerob)
      (list '$zeroa '$nz 0)
      (list '$zeroa '$zero 0)
      (list '$zeroa '$pz 0)
      (list '$zeroa '$pn 0)
      (list '$zeroa '$pnz 0)
      (list '$zeroa '$imaginary 0)
      (list '$zeroa  '$complex 0)

      ;; ind x {neg, nz, zero, pz, pos, pnz, imaginary, complex} either 0 or ind
	    (list '$ind '$zero 0)
      (list '$ind '$neg '$ind)
      (list '$ind '$nz '$ind)
      (list '$ind '$pz '$ind)
      (list '$ind '$pos '$ind)
      (list '$ind '$pnz '$ind)
      (list '$ind '$imaginary '$ind)
      (list '$ind '$complex '$ind)))

(defun mul-sign-extended-real (sgn x)
    (cond ((eql x 0) 0)
          (t (gethash (list x sgn) *extended-real-times-sign-mult-table* '$und))))

(defvar *zero* nil)    
;; Return the limit as var -> val of the product of the terms of the Common Lisp list of terms e.
;; The members of e can be explicit extended real numbers. Here is what we do:

;;   (a) loop thru the members of e and classify each term according to its limit.
;;   (b) if there is a subexpression that is a zero x infinity indeterminate form,
;;       attempt to simplify it using try-lospital-quit and adjust the various lists of terms
;;   (c) use the limit of product is product of limits rule using extended real number arithmetic.
(defun new-simplimtimes (e)
  (let ((const-inf-terms nil) ; terms that are explicitly either minf, inf, or infinity
        (const-zero-terms nil) ;terms that are explicitly either 0, zerob, or zeroa
        (inf-terms nil) ;terms whose limits are extended real numbers (but not explicitly so)
        (ind-terms nil) ;terms whose limit is ind
        (und-terms nil) ;terms whose limit is either und, nil, or true
        (zero-terms nil) ;terms whose limit is either zerob, 0, or zeroa
        (finite-terms nil)) ; all other terms, (real numbers)

    (dolist (ek e)
      (cond
        ((memq ek '($minf $inf $infinity))
         (push (cons ek ek) const-inf-terms))

		    ((or (eql ek 0) (memq ek '($zeroa $zerob)))
		       (push (cons ek ek) const-zero-terms))

        (t
	       (setq ek (infsimp ek))
         (let ((lim (limit ek var val 'think)))
           (cond ((memq lim '($minf $inf $infinity))
                    (push (cons lim ek) inf-terms))
                 ((or (eq lim '$ind) (eq lim nil) (eq lim t))
                    (push (cons lim ek) ind-terms))
                 ((eq lim '$und)
                    (push (cons lim ek) und-terms))
                 ((zerop2 lim)
                    (push (cons lim ek) zero-terms))
                 (t
                    (push (cons lim ek) finite-terms)))))))

	;; attempt to condense und-terms
	(when (and und-terms)
		(let* ((xxx (fapply 'mtimes (mapcar #'cdr und-terms)))
		       (w (limit1 xxx var val))) ; can be gruntz1
		(cond ((or (eq w '$und) (eq w t) (eq w nil))
		        (throw 'limit nil))

              ((memq w '($minf $inf $infinity))
			     (setq und-terms nil)
				 (push (cons w xxx) inf-terms))

              ((eq w '$ind)
               (setq und-terms nil)
			   (push (cons w xxx) ind-terms))

               ((zerop2 w)
                 (setq und-terms nil)
                 (push (cons w xxx) zero-terms))

               (t
			     (setq und-terms nil)
                 (push (cons w xxx) finite-terms)))))
		       
    ;; attempt to simplify indeterminate form zero × infinity using try-lhospital-quit
    (when (and zero-terms inf-terms)
      (let* ((a (fapply 'mtimes (mapcar #'cdr inf-terms)))
             (b (fapply 'mtimes (mapcar #'cdr zero-terms)))
             (w (limit2 a (div 1 b) var val)))
             ;(w (try-lhospital-quit b (div 1 a) nil)))
             ;(w (try-lhospital-quit a (div 1 b) t)))
        ;; lhospital failed, throw to limit
        (when (or (eq '$und w) (null w) (eq w t))
          (throw 'limit nil))

        (cond
          ((memq w '($minf $inf $infinity))
           (setq inf-terms (list (cons w w)))
           (setq zero-terms nil))

          ((eq w '$ind)
           (setq ind-terms (cons (cons w w) ind-terms))
           (setq inf-terms nil)
           (setq zero-terms nil))

          ((zerop2 w)
           (setq inf-terms nil)
           (setq zero-terms (list (cons w w))))

          (t
           (setq inf-terms nil)
           (setq zero-terms nil)
           (push (cons w w) finite-terms)))))

    (setq inf-terms (append inf-terms const-inf-terms))
	  (setq zero-terms (append zero-terms const-zero-terms))

    (cond
      ;; und × anything, so throw
      (und-terms (throw 'limit nil))

      ;; still an indeterminate form, so throw limit
	  ((and zero-terms inf-terms) (throw 'limit nil))

      (t  
         (let* ((finite-x (fapply 'mtimes (mapcar #'car finite-terms)))
                (ind-x (fapply 'mtimes (mapcar #'cdr ind-terms)))
			        	(zero-x (reduce #'mul-extended-real (mapcar #'car zero-terms) :initial-value 1))
                (inf-x (reduce #'mul-extended-real (mapcar #'car inf-terms) :initial-value 1)))
        
		(cond 
		    ;; infinite terms, no zero terms, and ind terms
		    ((and ind-terms inf-terms)
			    ;(mtell "branch a ~%")
				(mul-sign-extended-real ($csign (mul finite-x ind-x)) inf-x))

            ;; ind terms, zero terms no infinite terms
			((and ind-terms zero-terms)
			   ;(mtell "branch b ~%")
         (mul-sign-extended-real ($csign (mul finite-x ind-x)) zero-x))

            ;; ind terms, no infinite terms, no zero terms
			(ind-terms
			     ;(mtell "branch c ~%")
			   '$ind)

            ;; infinite terms no zero terms no ind terms
			(inf-terms 
			    ;(mtell "branch d ~%")
          ;(mtell "")
			    (mul-sign-extended-real ($csign finite-x) inf-x))

            ;; zero terms no infinite terms
			(zero-terms
			    ;(mtell "branch e ~%")
			    (mul-sign-extended-real ($csign finite-x) zero-x))

			;; just finite terms
			(t 
			  ; (mtell "branch f ~%")
			    finite-x)))))))