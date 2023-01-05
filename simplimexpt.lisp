;; Re-implementation of the function simplimexpt. The intent is for this 
;; code to be more easily fixed or extended, possibly more efficient, 
;; and more comphrensive than the standard function.

;; The standard simplimexpt has a reference to the special variable loginprod?, but
;; this code doesn't. Also, the standard simplimexpt has several calls to
;; ask-integer that this code doesn't. In part, I get by with fewer such questions by
;;  using zerob^b --> (-1)^b zeroa^b

;; Standard simplimexpt is about 110 LOC, but this is about three times longer. Maybe
;; I didn't leverage some other code that would make my code shorter--I'm not sure.
;; The hashtable consumes lots of lines of code, but it's conceptionally simple and
;; easy to modify.

;; bugs:
;;  (a) limit(4^(5+sin(x))^4,x,inf);

(in-package :maxima)
(declare-top (special var val lhcount lhp? *behavior-count-now*))

;; We know that limit(a,x,pt) = 1 and limit(b,x,pt) = inf. Return
;; limit(a^b,x,pt).
(defun $bob (a b x pt)
  (let* ((lhcount 0) (var x) (val pt) (*behavior-count-now* 0) (dir (behavior a x pt)) (ans))
	(cond ((eql dir -1) '$zeroa)
	      ((eq dir 1) '$inf)
	(car (errcatch (catch 'lhospital (bylog a b))))))

;; Dispatch Taylor, but recurse on the order until either the order 
;; reaches 128 or the Taylor polynomial is nonzero. When 
;; Taylor either fails to find a nonzero Taylor polynomial, return nil.

;; We set up a reasonable environment for calling taylor. 

(defun tlimit-taylor (e x pt n)
	(let ((ee 0) 
	      (silent-taylor-flag t) 
	      ($taylordepth 8)
		  ($taylor_logexpand nil)
		  ($maxtayorder t)
		  ($taylor_truncate_polynomials nil)
		  ($taylor_simplifier #'sratsimp))

        (setq ee ($ratdisrep (catch 'taylor-catch ($taylor e x pt n))))
		(cond ((and ee (not (alike1 ee 0))) 
		        ee)
              ((and ee (< n 128))
			    (tlimit-taylor e x pt (* 2 (max 1 n))))
			  (t nil))))

;; When limit(e,x,pt) = 0, we dispatch behavior to attempt to decide
;; if the limit is zerob, zeroa, or 0. 

;; I'm not sure why I'm using errcatch on behavior--is it due to a bug 
;; in behavior? Am I confused? Actually, I think calling behavior on
;; 1/x,x, inf fails.

;; If the call to taylor is needed, surely that functionality should be
;; wrapped into behavior.

(defmfun $behavior (e x pt)
  (let ((*behavior-count-now* 0))
	(behavior e x pt)))

(defvar *behavior-fails* nil)
(defun zero-fixup (e x pt)
   (let ((ee) (*behavior-count-now* 0))
   (when (eq pt '$inf)
	  (setq ee (resimplify ($ratdisrep (tlimit-taylor e x pt 1))))
	  (when ee
	     (setq e ee)))

   (let ((dir (errcatch (behavior e x pt))))
     (when (null dir)
	 	(push (ftake 'mlist e x pt) *behavior-fails*))
     (setq dir (if dir (car dir) 0))
	(cond ((eql dir -1) '$zerob)
		  ((eql dir 1) '$zeroa)
		  (t 0)))))

;; Return true iff a^b is 0^0, inf^0, or 1^inf, where by zero
;; we mean either zerob, 0, or zeroa; and by inf, we mean either
;; minf, inf, or infinity.		      
(defun mexpt-indeterminate-form-p (a b) ;0^0, inf^0, and 1^inf
 	(or (and (zerop2 a) (zerop2 b)) ;0^0
        (and (infinityp a) (zerop2 b)) ;inf^0
	    (and (eq t (meqp 1 a)) (infinityp b)))) ;1^inf

;; Return
;; inside if |e| < 1
;; one if e = 1
;; zero if e = 0
;; on id |e| = 1
;; pos-real-outside if real(e) > 1 & imag(e)=0
;; outside if |e| > 1
;; nil if all other tests fail.
(defun inside-outside-unit-circle (e)
	(setq e (risplit e))
	(let* ((re (car e)) (im (cdr e)) (x (add (mul re re) (mul im im))))
		(cond ((eq t (mgrp 1 x)) 'inside)
			  ((and (eq t (meqp im 0)) (eq t (meqp re 1))) 'one)
			  ((and (eq t (meqp 0 re)) (eq t (meqp 0 im))) 'zero)
			  ((eq t (meqp 1 x)) 'on)
			  ((and (eq t (meqp im 0)) (eq t (mgrp re 1))) 'pos-real-outside)
			  ((eq t (mgrp x 1)) 'outside)
			  (t nil))))

(defun mexpt-x^inf (x) ;return x^inf
    (let ((q (inside-outside-unit-circle (ridofab x))))
          (cond ((eq q 'inside) 0) ; (|x|<1)^inf = 0
				((eq q 'zero) 0) ;0^inf = 0
				((eq q 'one) 1) ;1^inf = 1
				((eq q 'on) '$ind) ; (|x|=1 & x =/= 1)^inf = ind
				((eq q 'pos-real-outside) '$inf) ;(x > 1)^inf = inf
				((eq q 'outside) '$infinity) ; (|x| > 1)^inf = infinity
				(t '$infinity))))

(defun mexpt-x^infinity (x) ;return x^infinity
    (let ((q (inside-outside-unit-circle (ridofab x))))
          (cond ((eq q 'inside) 0) ; (|x|<1)^infinity = 0
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
(defvar *extended-real-mexpt-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mexpt-table*) (third a)))
   (list 
       (list '$minf '$minf 0) 
	   (list '$minf '$zerob '$und) 
	   (list '$minf '$zeroa '$und) 
	   (list '$minf '$ind '$und) 
	   (list '$minf '$inf '$infinity) 
	   (list '$minf '$infinity '$infinity) 
	   (list '$minf '$und '$und) 

	   (list '$zerob '$minf '$und) 
	   (list '$zerob '$zerob '$und) 
	   (list '$zerob '$zeroa '$und) 
	   (list '$zerob '$ind '$und) 
	   (list '$zerob '$inf '$und) 
	   (list '$zerob '$und '$und) 
	   (list '$zerob '$infinity '$infinity)

	   (list '$zeroa '$minf '$und) 
	   (list '$zeroa '$zerob '$und) 
	   (list '$zeroa '$zeroa '$und) 
	   (list '$zeroa '$ind  '$und) 
	   (list '$zeroa '$und '$und) 

	   (list '$ind '$minf '$und) 
	   (list '$ind '$zerob '$und) 
	   (list '$ind '$zeroa '$und) 
	   (list '$ind '$ind '$und) 
	   (list '$ind '$inf '$und) 
	   (list '$ind '$infinity '$und) 
	   (list '$ind '$und '$und) 

	   (list '$inf '$ind '$und) 
	   (list '$inf '$inf '$inf) 
	   (list '$inf '$infinity '$infinity) 
	   (list '$inf '$und '$und) 

	   (list '$infinity '$minf '$infinity) 
	   (list '$infinity  '$zerob 1) 
	   (list '$infinity '$zeroa 1) 
	   (list '$infinity '$ind '$und) 
	   (list '$infinity '$inf  '$infinity) 
	   (list '$infinity  '$infinity '$infinity) 
	   (list '$infinity '$und '$und) 

	   (list '$und '$minf '$und) 
	   (list '$und '$zerob '$und) 
	   (list '$und '$zeroa '$und) 
	   (list '$und '$ind '$und) 
	   (list '$und '$inf '$und) 
	   (list '$und '$infinity '$und) 
	   (list '$und '$und '$und)))

(defvar *ht* nil)
(defvar *x* 0)
(defvar *c* nil)
(defvar *ind* nil)
(defvar *weird-fixup* 0)

;; *x* counts number of calls to simplim%mexpt--it's 5,414
;; *weird-fixup* counts number of times al = 2*zeroa and bl = -1 --it's 4 
;; *c* counts number of times simplim%mexpt gets to the end and gives up--it's 4
;; *nil-limit* is a list of limit problems where the limit is apparently nil--it's 4.

;; Redefine simplimexpt--simply call the new simplim%expt function.
(defun simplimexpt (a b al bl)
    (simplim%mexpt (list '(mexpt) a b) var val al bl))

(defun simplim%mexpt (e x pt &optional (al nil) (bl nil))
    (incf *x* 1)
	(let ((a (cadr e))
		  (b (caddr e)) ;e = a^b
		  (bb nil) (bre nil) (bim nil) (preserve-direction t))

       ;; When either al or bl are nil, evaluate their limits.
	    (when (null al)
		     (setq al (limit a x pt 'think))) ;al = limit of a
		(when (null bl)
	         (setq bl (limit b x pt 'think))) ;bl = limit of b

        ;; When bl = infinity, we need to look at the limits of the
		;; real and imaginary parts of b. These results are used in
		;; the rule exp(%i*inf + real) = ind. So for this case,
		;; we re-evaluate the limit of b.
		(when (eq bl '$infinity)
       	  (setq bb (risplit b))
		  (setq bre (limit (car bb) x pt 'think)) ;real part of limit of b
		  (setq bim (limit (cdr bb) x pt 'think))) ;imaginary part of limit of b

		;; When al=0 and bl < 0, dispatch zero-fixup in an effort to decide if
		;; the limit is zerob, 0, or zeroa.
		(when (and (eql al 0) (eq t (mgrp 0 bl)))
			(setq al (zero-fixup a x pt)))
		(cond 
		    ;; Hashtable look up for the limit. This handles the determinate 
			;; cases for extended^extended. Currently, the testsuite only
			;; tests the cases [[zeroa,zerob],[inf,inf],[inf,zeroa],[infinity,inf]]
			((gethash (list al bl) *extended-real-mexpt-table* nil))

	        ;; Special case 0^-1. Previously, we made sure that al can't be either
			;; zerob or zeroa, so we return infinity for 0^-1.
			((and (eql al 0) (eq t (mgrp 0 bl))) '$infinity)

			;; Yikes!--this is clumsy workaround for a bug. Running the testsuite,
			;; this workaround is used four times. Of course, this should be
			;; generalized to trap constant * zeroa & constant * zerob.
			((and (alike1 al (mul 2 '$zeroa)) (eql b -1))
			    (incf *weird-fixup* 1)
				'$inf)

			;; For an indeterminate form, dispatch bylog
			((mexpt-indeterminate-form-p al bl)
		        (push (ftake 'mlist a b al bl x pt) *ind*)
				(let ((var x) (val pt) (lhcount 0) (ans))
				  (setq ans (catch 'lhospital (bylog a b)))
				  (or ans (throw 'limit nil))))

   			;; Limit by direct substitution.
			((and al bl (not (extended-real-p al)) (not (extended-real-p bl)))
			    (ftake 'mexpt (ridofab al) (ridofab bl)))

            ;; exp(%i*inf + real) = ind & exp(%i*minf + real) = ind
            ((and (eq al '$%e) 
			        (or (eq bim '$inf)  (eq bim '$minf))
			        (not (extended-real-p bre)))
			    '$ind)

            ;; When bl is an extended real...maybe split this off as a function.
			((extended-real-p bl)
			    (cond ((eq bl '$minf) ;a^minf
			             (mexpt-x^minf al))
                      ((eq bl '$zerob) 1) ;a1^zerob --> 1
	                  ((eq bl '$zeroa) 1) ;a1^zeroa --> 1
					  ((eq bl '$ind)
						    (if (eq t (mgrp al 0)) '$ind '$und))
					  ((eq bl '$und) '$und) ;are you sure? 
                      ((eq bl '$inf) ;a^inf 
			               (mexpt-x^inf al))
					  ((eq bl '$infinity)
						   (mexpt-x^infinity al))
					  ;((gethash (list al bl) *extended-real-mexpt-table* nil))
					  (t 
					    (throw 'limit nil))))

			;; When al is an extended real, dispatch mexpt-extended^b
			((extended-real-p al) (mexpt-extended^b al bl))
			;; Give up--shouldn't happen, but it does--sometimes limit returns
			;; nil. I should look into that. 	 
			(t 
			    (push (ftake 'mlist al bl) *c*)
			    (throw 'limit nil)))))
(setf (get 'mexpt 'simplim%function) 'simplim%mexpt)