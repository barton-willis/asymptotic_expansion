;; This is a re-implementation of the function simplimexpt. The intent is for this 
;; code to be more easily fixed or extended, possibly more efficient, and more 
;; comphrensive than the standard function.

;; Differences: The standard simplimexpt has a reference to the special variable 
;; loginprod?, but; this code doesn't. Also, the standard simplimexpt has several 
;; calls to ask-integer that this code doesn't. In part, I get by with fewer
;; such questions by using zerob^b --> (-1)^b zeroa^b

;; Standard simplimexpt is about 110 lines of code, but this is about three times 
;; longer. Maybe I didn't leverage some other code that would make my code shorter.

(in-package :maxima)
	
(declare-top (special var val lhcount lhp? *behavior-count-now*))

;; When limit(e,x,pt) = 0, we dispatch behavior to attempt to decide
;; if the limit is zerob, zeroa, or 0. The function behavior misses 
;; some cases that it might. At one time this code caught a few more
;; cases by dispatching taylor. But let's not do that
(defun zero-fixup (e x pt)
   (let ((*behavior-count-now* 0) (dir (behavior e x pt)))
	(cond ((eql dir -1) '$zerob)
		  ((eql dir 1) '$zeroa)
		  (t 0))))

;; Return true iff a^b is 0^0, inf^0, or 1^inf, where by zero
;; we mean either zerob, 0, or zeroa; and by inf, we mean either
;; minf, inf, or infinity.		      
(defun mexpt-indeterminate-form-p (a b) ;0^0, inf^0, and 1^inf
 	(or (and (zerop2 a) (zerop2 b)) ;0^0
        (and (infinityp a) (zerop2 b)) ;inf^0
	    (and (eq t (meqp 1 a)) (infinityp b)))) ;1^inf

;; Return
;;  (a) pos-real-inside if 0 < x < 1
;;  (b) inside if |e| < 1
;;  (c) one if e = 1
;;  (d) zero if e = 0
;;  (e) on id |e| = 1
;;  (f) pos-real-outside if real(e) > 1 & imag(e)=0
;;  (g) outside if |e| > 1
;;  (h) nil if all other tests fail
(defun inside-outside-unit-circle (e)
	(setq e (risplit e))
	(let* ((re (car e)) (im (cdr e)) (x (add (mul re re) (mul im im))))
		(cond ((and (eql im 0) (eq t (mgrp re 0)) (eq t (mgrp 1 re)))
		       'pos-real-inside)		
		((eq t (mgrp 1 x)) 'inside)
			  ((and (eq t (meqp im 0)) (eq t (meqp re 1))) 'one)
			  ((and (eq t (meqp 0 re)) (eq t (meqp 0 im))) 'zero)
			  ((eq t (meqp 1 x)) 'on)
			  ((and (eq t (meqp im 0)) (eq t (mgrp re 1))) 'pos-real-outside)
			  ((eq t (mgrp x 1)) 'outside)
			  (t nil))))

(defun mexpt-x^inf (x) ;return x^inf
    (let ((q (inside-outside-unit-circle (ridofab x))))
          (cond ((eq q 'zero) 0) ;0^inf = 0
		        ((eq q 'pos-real-inside) '$zeroa)
		        ((eq q 'inside) 0)
				((eq q 'zero) 0) ;0^inf = 0
				((eq q 'one) 1) ;1^inf = 1
				((eq q 'on) '$ind) ; (|x|=1 & x =/= 1)^inf = ind
				((eq q 'pos-real-outside) '$inf) ;(x > 1)^inf = inf
				((eq q 'outside) '$infinity) ; (|x| > 1)^inf = infinity
				(t '$infinity))))

(defun mexpt-x^infinity (x) ;return x^infinity
    (let ((q (inside-outside-unit-circle (ridofab x))))
          (cond ((eq q 'inside) 0) ; (|x|<1)^infinity = 0
		        ((eq q 'pos-real-inside) 0) ;(0 < x < 1)^infinity = 0
				((eq q 'zero) 0) ;0^infinity = 0
				((eq q 'one) 1) ;1^infinity = 1
				((eq q 'on) '$und) ; (|x|=1 & x =/= 1)^infinity = und
				((eq q 'pos-real-outside) '$infinity) ;(x > 1)^infinity= infinity
				((eq q 'outside) '$infinity) ; (|x| > 1)^infinity = infinity
				(t '$infinity))))

(defun mexpt-x^minf (x) ;return x^minf
  (let ((q (mexpt-x^inf x)))
	(cond ((eql q 0) '$infinty)
	      ((eql q 1) 1)
		  ((eq q '$ind) '$ind)
		  ((eq q '$inf) 0)
		  ((eq q '$infinity) 0)
		  (t (throw 'limit nil )))))

;; Return a^b, where b is an extended real and a isn't an extended real.
(defun mexpt-a^extended (a b)
    (cond ((eq b '$minf) ;a^minf
			(mexpt-x^minf a))
          ((eq b '$zerob) 1) ;a^zerob --> 1
	      ((eq b '$zeroa) 1) ;a1^zeroa --> 1
		  ((eq b '$ind)
			(if (eq t (mgrp a 0)) '$ind '$und))
		  ((eq b '$und) '$und) ;are you sure? 
          ((eq b '$inf) ;a^inf 
			 (mexpt-x^inf a))
		  ((eq b '$infinity)
			(mexpt-x^infinity a))
		  (t (throw 'limit nil))))

;; Return a^b, where a is an extended real and b isn't an extended real.
(defun mexpt-extended^b (a b)
 (let ((sgn (let ((*complexsign* t))
        (if *getsignl-asksign-ok* ($asksign b) ($sign b)))))
    ;; Should there cases for pn, pz, or nz?
	(cond ((eq a '$minf)
	        (cond ((eq sgn '$neg) 0) ; minf^neg --> 0
				  ((eq sgn '$zero) (throw 'limit nil)) ;minf^zero --> throw
				  ((eq sgn '$pos) (mul (ftake 'mexpt -1 b) '$inf))
				  (t (throw 'limit nil))))

		  ((eq a '$zerob)
			(mul (ftake 'mexpt -1 b) (simplimexpt '$zeroa b '$zeroa b)))

		  ((eq a '$zeroa)
			(cond ((eq sgn '$neg) '$inf)  ; zeroa^neg --> inf
			      ((eq sgn '$pos) '$zeroa) ; zero^pos --> zeroa
				  (t (throw 'limit nil))))

		  ((eq a '$ind)
			(cond ((eq sgn '$neg) '$und)  ; ind^neg --> und
			      ((eq sgn '$zero) 1)       ; ind^0 --> 1. 
				  ((eq sgn '$pos) '$ind) ; ind^pos --> ind
				  (t (throw 'limit nil))))

		  ((eq a '$und) '$und) ;und^anything = und

		  ((eq a '$inf)
		    (cond ((eq sgn '$neg) '$zeroa) ; inf^neg --> zeroa
				  ((eq sgn '$pos) '$inf) ; inf^pos --> inf
				  (t (throw 'limit nil))))

		  ((eq a '$infinity)
			 (cond ((eq sgn '$neg) 0) ; infinity^neg --> 0
				   ((eq sgn '$pos) '$infinity) ; infinty^pos --> infinity
                   (t (throw 'limit nil))))
		 (t (throw 'limit nil)))))
	
;; We use a hashtable to represent unambiguous cases of extended^extended, where
;; extended in {minf,zerob, zeroa, ind, inf, infinity, und}. The ambiguous cases
;; are zeroa^zeroa, zeroa^zerob, zerob^zeroa, and zerob^zerob.
(defvar *extended-real-mexpt-table-xxx* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mexpt-table-xxx*) (third a)))
   (list 
       (list '$minf '$minf 0) 
	   (list '$minf '$inf '$infinity) 
	   (list '$minf '$infinity '$infinity) 

	   (list '$zerob '$inf 0) 
	   (list '$zerob '$infinity '$infinity)

	   (list '$zeroa '$inf '$zeroa)

	   (list '$inf '$inf '$inf) 
	   (list '$inf '$infinity '$infinity) 

	   (list '$infinity '$minf '$infinity) 
	   (list '$infinity '$inf '$infinity) 
	   (list '$infinity '$infinity '$infinity)))

(defvar *x* 0)
(defvar *c* nil)
(defvar *ind* nil)
;; Redefine simplimexpt--simply call the new simplim%expt function.

(defvar *d* nil)
(defvar *new* 0)

(defun simplimexpt (a b al bl)
	(simplim%mexpt (list '(mexpt) a b) var val al bl))

(defun simplim%mexpt (e x pt &optional (al nil) (bl nil))
    (incf *x* 1)
	(let* ((a (cadr e))
		   (b (caddr e)) ;e = a^b
		   (bb nil) (re nil) (im nil) (bre nil) (bim nil) (preserve-direction t))

		;; When both a & b depend on x, use a^b = exp(b log(a)).
		;; We also re-do the limits of a & b.
	    (when (and (among x a) (among x b))
			(setq b (mul b (ftake '%log a))
			      a '$%e)
			(setq al '$%e
			      bl (limit b x pt 'think)))

       ;; When either al or bl are nil, evaluate their limits. This
	   ;; can happen when simplim%mexpt is called directly (not from
	   ;; simplimexpt)
	    (when (null al)
		     (setq al (limit a x pt 'think))) ;al = limit of a
		(when (null bl)
	         (setq bl (limit b x pt 'think))) ;bl = limit of b

        ;; When bl = infinity, we need to look at the limits of the
		;; real and imaginary parts of b. These results are used in
		;; the rule exp(%i*inf + real) = ind. So for this case,
		;; we find the real and imaginary parts of the limit of b.
		(when (eq bl '$infinity)
       	  (setq bb (risplit b))
		  (setq bre (limit (car bb) x pt 'think)) ;real part of limit of b
		  (setq bim (limit (cdr bb) x pt 'think))) ;imaginary part of limit of b

		;; When al=0 dispatch zero-fixup. This is an effort to decide if
		;; the limit could be either zerob, or zeroa instead of 0. 
		;; This conversion causes a number of semantic testsuite failures.
		;; If the check is only done when bl < 0, these failures don't happen.
		(when (eql al 0) ;(eq t (mgrp 0 bl)))
			(setq al (zero-fixup a x pt)))
		(when (eql bl 0)
			(setq bl (zero-fixup b x pt)))
	    
		(cond 
		    ;; Hashtable look up for the limit. This handles the determinate 
			;; cases for extended^extended. Currently, the testsuite only
			;; tests the cases ($zeroa $inf), ($infinity $inf), and
			;; ($infinity $inf)) 			
			((gethash (list al bl) *extended-real-mexpt-table-xxx* nil))

	        ;; Special case 0^(negative real). Previously, we made sure that 
			;; Maxima is unable to determine that al could be either zerob or 
			;; zeroa. I don't think returning infinity is correct here, so we
			;; give up.
			((and (eql al 0) (eq t (mgrp 0 bl))) 
			  (throw 'limit nil))

			;; For an indeterminate form, dispatch bylog
			((mexpt-indeterminate-form-p al bl)
		        (push (ftake 'mlist a b al bl x pt) *ind*)
				(let ((var x) (val pt) (lhcount 0) (ans))
				  (setq ans (catch 'lhospital (bylog b a)))
				  (or ans (throw 'limit nil))))
			
			;; Special case: al in (-infty,0).
			((and (not (extended-real-p bl)) 
			      (not (extended-real-p al)) 
			      (eq t (mgrp 0 al)))
			  ;; Toward the limit point, we need to know the sign of the 
			  ;; imaginary part of a. 
			  (setq a (risplit a))
			  (setq re (car a))
			  (setq im (cdr a))
			  (setq im (zero-fixup im x pt))
			  (cond ((eq im '$zerob)
			         ;; (x - %i 0^(+))^bl  --> |x|^bl exp(-%i %pi bl)
			         (mul (ftake 'mexpt (ftake 'mabs re) bl)
					      (let (($demoivre t)) 
						         (ftake 'mexpt '$%e (mul -1 '$%i '$%pi bl)))))
					;; (x + %i 0^(+))^integer  --> (x)^integer
					((and (eql im 0) (or t (eq '$yes (ask-integer bl '$integer))))
					  (ftake 'mexpt al bl))
                    ;; (x + %i 0^(+))^bl  --> |x|^bl exp(%i %pi bl)
					((or (eq im '$zeroa) (eql im 0))
			         (mul (ftake 'mexpt (ftake 'mabs re) bl)
					      (let (($demoivre t)) 
					         (ftake 'mexpt '$%e (mul '$%i '$%pi bl)))))
					;; give up
					(t 
					 (throw 'limit nil))))	  
   			;; OK to use limit(a^b,x,pt) = limit(a,x,pt)^limit(b,x,pt).

			;; For limits such as limit(x^x,x,3/4), it would be nicer
			;; to get (3/4)^(3/4) instead of %e^((3*log(3/4))/4).

			;; This is wrong when al in (-minf,0) and bl isn't an integer
			((and al bl (not (extended-real-p al)) (not (extended-real-p bl)))
			    (ftake 'mexpt (ridofab al) (ridofab bl)))

            ;; exp(%i*inf + real) = ind & exp(%i*minf + real) = ind
            ((and (eq al '$%e) 
			        (or (eq bim '$inf) (eq bim '$minf))
			        (not (extended-real-p bre)))
			    '$ind)
            ;; (nonvanishing ind)^real = ind
			((and (eq al '$ind) ; (ind =\= 0)^real
			      (not (extended-real-p a))
			      (eq t (mnqp a 0)) 
				  (not (extended-real-p bl)))			  
				;(incf *new* 1)
			  '$ind)

            ;; When bl is an extended real, dispatch mexpt-a^extended
			((extended-real-p bl) (mexpt-a^extended al bl))

			;; When al is an extended real, dispatch mexpt-extended^b
			((extended-real-p al) (mexpt-extended^b al bl))
			;; Give up--shouldn't happen	 
			(t 
			    (push (ftake 'mlist al bl) *c*)
			    (throw 'limit nil)))))
(setf (get 'mexpt 'simplim%function) 'simplim%mexpt)
