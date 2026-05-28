#|

Error(s) found:
  /rtest15.mac problems:  (210 425)
  /rtest16.mac problems:  (525 809)
  /rtestint.mac problems: (152 237 241)
  /rtest_gamma.mac problem:  (477)
  /rtest_sqrt.mac problems:  (9 11 12)
  /rtest_limit.mac problems:  (15 62 64 163 164 232 278)
   /rtest_limit_extra.mac problems:  (54 55 63 64 66 67 81 94 208 266 301 308 309 400 401 411 422)
Tests that were expected to fail but passed:
  /rtest_limit.mac problem:  (113)
  /rtest_limit_extra.mac problems:  (268 269 270)
35 tests failed out of 14,926 total tests.

 |#

(in-package :maxima)

(declare-top (special origval
		      *indicator numer denom exp var val
		      taylored logcombed *integer-info* *old-integer-info*
		      $exponentialize lhp? lhcount
		      loginprod? context limit-assumptions
		      limit-top))

(mfuncall '$declare '*complex-infinitesimal* '$complex)
(mfuncall '$assume (ftake '$notequal '*complex-infinitesimal* 0))
(unless (fboundp 'old-simplimtimes)
  (setf (symbol-function 'old-simplimtimes)
        (symbol-function 'simplimtimes)))

(defvar *lal* nil)
(defvar *yikes* nil)
(defun simplimtimes (e)
  (let ((old (old-simplimtimes e))
        (new (new-simplimtimes e)))


    (when (not preserve-direction)
      (setq old (ridofab old))
      (setq new (ridofab new)))

    (when (not (alike1 old new))
      (push (ftake 'mlist (fapply 'mlist e) old new var val) *yikes*))
    
    new))

(defun $report ()
  (fapply 'mlist *yikes*))

(defun xsign (e)
   (let ((cntx ($supcontext)))
    (unwind-protect
        (progn
          ;; Set up assumptions for the super context
          (assume (ftake 'mgreaterp '$zeroa 0))
          (assume (ftake 'mgreaterp 0 '$zerob))
          (assume (ftake 'mgreaterp (div 1 100) '$zeroa))
          (assume (ftake 'mgreaterp '$zerob (div -1 100)))
          ;; Determine which function to call based on *getsignl-asksign-ok*
          ($csign e))
      ;; remove the super context
      ($killcontext cntx))))  



(defparameter *debug-limit* nil)

(defun debug-mtell (&rest args)
  (when *debug-limit*
    (apply #'mtell args)))

;; We use a hashtable to represent the multiplication table for extended
;; real numbers. The table is symmetric, so we list only its "upper" half.
;; When a value isn't found in the hashtable, mult-extended-real returns `$und`,
;; so we omit entries for those cases.

;; This multiplication is commutative and associative, but not distributive. For example, 
;; inf*(inf + zeroa) = inf, but inf * inf + inf * zeroa = und.
(defvar *extended-real-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) 
      (setf (gethash (list (first a) (second a)) *extended-real-mult-table*) (third a))
      (setf (gethash (list (second a) (first a)) *extended-real-mult-table*) (third a)))
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
         (list '$inf '$minf '$minf)
         (list '$inf '$infinity '$infinity)

         (list '$infinity '$infinity '$infinity)
         (list '$infinity '$inf '$infinity)
         (list '$ind 0 0)
         (list '$ind '$zerob 0)
         (list '$ind '$zeroa 0)
         (list '$ind '$ind '$ind)))

(defun mul-extended-real (a b)
  "Multiply `a` and `b`, where each is either an extended real or one.
   If both are extended reals, look up their product in *extended-real-mult-table*.
   The table is symmetric: first try `(a,b)`, then `(b,a)`. If neither is found, return `$und`."


  (when (not (member a '($minf $zerob $zeroa $ind '$und '$inf '$infinity)))
     (setq a (infsimp a)))

(when (not (member b '($minf $zerob $zeroa $ind '$und '$inf '$infinity)))
     (setq b (infsimp b)))

  (when (and
            (not (onep a))
            (not (onep b))
            (not (gethash (list a b) *extended-real-mult-table*))
            (not (gethash (list a b) *extended-real-mult-table*)))
      (push (ftake 'mlist a b) *lal*))
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

      ;; zeroa x {neg, nz, zero, pz, pn, pos, pnz, imaginary, complex} is a zero
      (list '$zeroa '$pos '$zeroa)
	    (list '$zeroa '$neg '$zerob)
      (list '$zeroa '$nz 0)
      (list '$zeroa '$zero 0)
      (list '$zeroa '$pz 0)
      (list '$zeroa '$pn 0)
      (list '$zeroa '$pnz 0)
      (list '$zeroa '$imaginary 0)
      (list '$zeroa '$complex 0)

      ;; ind x {neg, nz, zero, pz, pn, pos, pnz, imaginary, complex} either 0 or ind
	    (list '$ind '$zero 0)
      (list '$ind '$neg '$ind)
      (list '$ind '$nz '$ind)
      (list '$ind '$pz '$ind)
      (list '$ind '$pn '$ind)
      (list '$ind '$pos '$ind)
      (list '$ind '$pnz '$ind)
      (list '$ind '$imaginary '$ind)
      (list '$ind '$complex '$ind)))


(defmfun $jqm ()
  (fapply 'mlist *lal*))

(defun mul-sign-extended-real (sgn x)

    (cond ((eql x 0) 0) ; 0 x {any sign} = 0
          (t 
          
           (when (not (gethash (list x sgn) *extended-real-times-sign-mult-table*))
            (push (ftake 'mlist x sgn) *lal*))
          (gethash (list x sgn) *extended-real-times-sign-mult-table* '$und))))

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
         (let* ((lim (limit ek var val 'think)))
           ;; When the limit is 0, use csign to attempt to decide if the result
           ;; could be either zerob or zeroa. Alternatively, we could try zero-fixup.
           ;; This hack is needed for limit(exp(x)*(gamma(x + exp(- x)) - gamma(x)), x, inf);
           (when (eql 0 lim)
             (let ((sgn ($csign ek)))
               (setq lim (cond ((eq sgn '$neg) '$zerob)
                               ((eq sgn '$pos) '$zeroa)
                               (preserve-direction (zero-fixup ek var val))
                               (t 0)))))

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
	(when (and und-terms (cdr und-terms))
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
        ;; this breaks integrate(x*sin(x)*exp(-x^2),x,minf,inf);
		    ((and ind-terms inf-terms)
            (debug-mtell "branch a ~%")
		    		(mul-sign-extended-real ($csign (mul finite-x ind-x)) inf-x))

            ;; ind terms & zero terms no infinite terms
			((and ind-terms zero-terms)
			   (debug-mtell "branch b ~%")
         (mul-sign-extended-real ($asksign (mul finite-x ind-x)) zero-x))

      ;; ind terms, no infinite terms, no zero terms
			(ind-terms
			     (debug-mtell "branch c ~%")
			   '$ind)

            ;; infinite terms no zero terms no ind terms
			(inf-terms 
			    (debug-mtell "branch d sgn = ~M ; inf-x = ~M  ~%" ($csign finite-x) inf-x)
			    (mul-sign-extended-real ($asksign finite-x) inf-x))

            ;; zero terms no infinite terms
			(zero-terms
			    (debug-mtell "branch e sgn = ~M ; zero-x = ~M ~%" ($csign finite-x) zero-x)
          (let ((z (risplit finite-x)))
             (add 
                (mul-sign-extended-real ($csign (car z)) zero-x)
                (mul '$%i (mul-sign-extended-real ($csign (cdr z)) zero-x)))))
;(mult finite-x zero-x))
          ;(mul-sign-extended-real ($csign finite-x) zero-x))

			;; just finite terms
			(t 
			   (debug-mtell "branch f ~%")
			    finite-x)))))))

(defun ridofab (e)
  (maxima-substitute 0 '$zeroa (maxima-substitute 0 '$zerob (maxima-substitute 0 '*complex-infinitesimal* e))))