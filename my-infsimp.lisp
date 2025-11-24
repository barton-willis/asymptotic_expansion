;;; Copyright (c) Barton Willis 2023, 2025

;;; GNU GENERAL PUBLIC LICENSE Version 3, 29 June 2007
;;; For details, see the file LICENSE

#|  
Maxima’s general simplifier is responsible for incorrectly simplifying inf - inf to 0, 0*inf to 0, and 
several other such bugs. This code does not fix these bugs, but it does rework the Maxima functions 
simpinf, infsimp, and simpab. The one-argument limit function is the sole user interface to this code. 
For example, limit(ind^2 + %pi) evaluates to ind, and limit(inf^2 + zerob) evaluates to inf. 

This code has three internal functions. They are simpinf, infsimp, and simpab. The main function is 
simpab. The identical functions simpinf and infsimp call simpab followed by setting both
zeroa and zerob to zero. 

Addition and multiplication of extended real numbers are commutative and associative,but there are 72 violations
of distributivity. The violations are (the first member represents infinity*(infinity +inf) = infinity*und =
und, but infinity*infinity+infinity*inf = infinity + infinity = infinity.)

[[infinity, infinity, inf], [infinity, infinity, ind],
[infinity, infinity, zeroa], [infinity, infinity, zerob],
[infinity, infinity, minf], [infinity, inf, infinity], [infinity, inf, ind],
[infinity, inf, zeroa], [infinity, inf, zerob], [infinity, inf, minf],
[infinity, ind, infinity], [infinity, ind, inf], [infinity, ind, minf],
[infinity, zeroa, infinity], [infinity, zeroa, inf], [infinity, zeroa, minf],
[infinity, zerob, infinity], [infinity, zerob, inf], [infinity, zerob, minf],
[infinity, minf, infinity], [infinity, minf, inf], [infinity, minf, ind],
[infinity, minf, zeroa], [infinity, minf, zerob], [inf, infinity, ind],
[inf, infinity, zeroa], [inf, infinity, zerob], [inf, inf, ind],
[inf, inf, zeroa], [inf, inf, zerob], [inf, ind, infinity], [inf, ind, inf],
[inf, ind, minf], [inf, zeroa, infinity], [inf, zeroa, inf],
[inf, zeroa, minf], [inf, zerob, infinity], [inf, zerob, inf],
[inf, zerob, minf], [inf, minf, ind], [inf, minf, zeroa], [inf, minf, zerob],
[ind, zeroa, zeroa], [ind, zeroa, zerob], [ind, zerob, zeroa],
[ind, zerob, zerob], [zeroa, zeroa, zeroa], [zeroa, zeroa, zerob],
[zeroa, zerob, zeroa], [zeroa, zerob, zerob], [zerob, zeroa, zeroa],
[zerob, zeroa, zerob], [zerob, zerob, zeroa], [zerob, zerob, zerob],
[minf, infinity, ind], [minf, infinity, zeroa], [minf, infinity, zerob],
[minf, inf, ind], [minf, inf, zeroa], [minf, inf, zerob],
[minf, ind, infinity], [minf, ind, inf], [minf, ind, minf],
[minf, zeroa, infinity], [minf, zeroa, inf], [minf, zeroa, minf],
[minf, zerob, infinity], [minf, zerob, inf], [minf, zerob, minf],
[minf, minf, ind], [minf, minf, zeroa], [minf, minf, zerob]]


The semantic testsuite failures are (this requires a tweak in limit as well)


********************* rtest_sqrt.mac: Problem 9 (line 45) *********************

Input:
limit([sqrt(inf), sqrt(- inf), sqrt(minf), sqrt(- minf), sqrt(infinity)])


Result:
[inf, %i inf, %i inf, inf, infinity]

This differed from the expected result:
[inf, infinity, infinity, inf, infinity]

******************* rtest_limit.mac: Problem 232 (line 874) *******************

Input:
        1/x
limit((x    - 1) sqrt(x), x, 0, minus)


Result:
%i inf

This differed from the expected result:
infinity

******************** rtest_trace.mac: Problem 87 (line 342) *******************

Input:
(untrace(rischint), trace(integrate, defint, limit, antideriv),
with_stdout(S, block([display2d : false],
integrate(exp(- x) cos(x), x, 0, inf))), get_output_stream_string(S))


Result:
1 Call   integrate [%e^-x*cos(x),x,0,inf]
 1 Call   defint [%e^-x*cos(x),x,0,inf]
  1 Call   limit [0]
  1 Return limit 0
  1 Call   limit [%e^-x,x,inf]
  1 Return limit 0
  1 Call   limit [0]
  1 Return limit 0
  1 Call   antideriv [%e^-x*cos(x),x]
  1 Return antideriv (%e^-x*(sin(x)-cos(x)))/2
  1 Call   limit [0]
  1 Return limit 0
  1 Call   limit [(%e^-x*sin(x))/2-(%e^-x*cos(x))/2,x,0,plus]
  1 Return limit -(1/2)
  1 Call   limit [(%e^-x*sin(x))/2-(%e^-x*cos(x))/2,x,inf,minus]
  1 Return limit 0
 1 Return defint 1/2
1 Return integrate 1/2

This differed from the expected result:
1 Call   integrate [%e^-x*cos(x),x,0,inf]
 1 Call   defint [%e^-x*cos(x),x,0,inf]
  1 Call   limit [0]
  1 Return limit 0
  1 Call   limit [%e^-x,x,inf]
  1 Return limit 0
  1 Call   limit [0]
  1 Return limit 0
  1 Call   antideriv [%e^-x*cos(x),x]
  1 Return antideriv (%e^-x*(sin(x)-cos(x)))/2
  1 Call   limit [0]
  1 Return limit 0
  1 Call   limit [(%e^-x*sin(x))/2-(%e^-x*cos(x))/2,x,0,plus]
   2 Call   limit [zerob]
   2 Return limit 0
  1 Return limit -(1/2)
  1 Call   limit [(%e^-x*sin(x))/2-(%e^-x*cos(x))/2,x,inf,minus]
  1 Return limit 0
 1 Return defint 1/2
1 Return integrate 1/2

99/100 tests passed

The following 1 problem failed: (87)

Running tests in rtest_limit_extra:
***************** rtest_limit_extra.mac: Problem 94 (line 321) ****************

Input:
        1/x
limit((x    - 1) sqrt(x), x, 0, minus)


Result:
%i inf

This differed from the expected result:
infinity

|#
(in-package :maxima)
;;; Code for simpab, simpinf, and infsimp
(defun extended-real-p (e)
  "Return true if `e` is a symbol and an element of *extended-reals*. The seven extended
   reals are `minf`, `zerob`, `zeroa`, `ind`, `inf`, `infinity`, and `und`."
  (and (symbolp e) (member e *extended-reals*)))

(defun nonzero-p (e)
  "Return `t` if `e` is not `eql` to 0, nil otherwise. This function does a syntactic, not semantic check 
   for a vanishing input. In particular, this function returns nil for both `zerob` and `zeroa`."
  (not (eql e 0)))

;; Maybe there should be an askcsign that has the option of saving the result in the 
;; current environment.
(defun maybe-asksign (e)
  "Dispatch to either $asksign or $csign depending on *getsignl-asksign-ok*."
  (if *getsignl-asksign-ok*
      ($asksign e)
      ($csign e)))

;; We use a hashtable to represent the multiplication table for extended
;; real numbers. The table is symmetric, so we list only its "upper" half.
;; When a value isn't found in the hashtable, mult-extended-real returns `und`,
;; so we omit entries for those cases.

;; This multiplication is commutative and associative, but not distributive. For example, 
;; inf*(inf + zeroa) = inf, but inf * inf + inf * zeroa = und.
(defvar *extended-real-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mult-table*) (third a)))
   (list (list '$minf '$minf '$inf)
         (list '$minf '$inf '$minf)
         (list '$minf '$infinity '$infinity)

         (list '$zerob '$zerob '$zeroa)
         ;(list '$zerob '$ind '$ind) ;maybe would be OK to define zeroa x ind = 0 & zerob x ind = 0
         ;(list '$zeroa '$ind '$ind)
         (list '$zerob '$zeroa '$zerob)
         (list '$zeroa '$zeroa '$zeroa)
         
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

(defun mul-extended (l)
  "Map `simpab` on the CL list `l`, then separately multiply the members of `l` that are extended 
   reals and those that are not. Finally, return the product of the extended reals times the non-extended 
   reals, but do not simplify this product further--for example, return 42 x inf, not inf."
  (let ((extended 1) 
        (non-extended 1)
        (preserve-direction t))
	  (dolist (lk l)
        (setq lk (simpab lk))
        (if (extended-real-p lk) 
		        (setq extended (mul-extended-real lk  extended))
			      (setq non-extended (mul non-extended lk))))
	  (mul extended non-extended)))

(defvar *extended-real-mexpt-table* (make-hash-table :test #'equal))
;;When a key (a,b) isn't in the hashtable, the default is that a^b is und.
(mapcar #'(lambda (a) 
  (setf (gethash (list (first a) (second a)) *extended-real-mexpt-table*) (third a)))
   (list 
   (list '$minf '$minf 0)              ;minf^minf = 0
   (list '$minf '$inf '$infinity)      ;minf^inf = infinity
   (list '$minf '$infinity '$infinity) ;minf^infinity = infinity

   (list '$zerob '$ind '$ind)          ;zerob^ind = ind (not sure)
   (list '$zerob '$inf 0)              ;zerob^inf = 0 (not sure)
   (list '$zerob '$infinity 0)         ;zerob^infinity = 0 (not sure)

   (list '$zeroa '$ind '$ind)          ;zeroa^ind = ind
   (list '$zeroa '$inf 0)              ;zeroa^inf = 0  
   (list '$zeroa '$infinity 0)         ;zeroa^infinity = 0

   (list '$inf '$minf 0)               ;inf^minf = 0
   (list '$inf '$inf '$inf)            ;inf^inf = inf
   (list '$inf '$infinity '$infinity)  ;inf^infinity = infinity

   (list '$infinity '$minf '$infinity) ;infinity^minf = infinity
   (list '$infinity '$inf '$infinity)  ;infinity^inf = infinity
   (list '$infinity '$infinity '$infinity))) ;infinity^infinity = infinity

(defun mexpt-extended (a b)
  (let ((preserve-direction t))
    (setq a (simpab a))
    (setq b (simpab b))
  (cond
    ;; Lookup in table
    ((and
       (member a *extended-reals*)
       (member b *extended-reals*)
       (gethash (list a b) *extended-real-mexpt-table* '$und)))

    ((and (integerp b) 
          ($polynomialp a (ftake 'mlist '$zeroa) #'(lambda (q) (freeofl q *extended-reals*)))
          (nonzero-p (ridofab a)))
        (ridofab (ftake 'mexpt a b)))
      ;($ratdisrep ($taylor (ftake 'mexpt a b) '$zeroa 0 1)))

    ((and (integerp b) 
          ($polynomialp a (ftake 'mlist '$zerob) #'(lambda (q) (freeofl q *extended-reals*)))
          (nonzero-p (ridofab a)))
       (ridofab (ftake 'mexpt a b)))    
     ;; ($ratdisrep ($taylor (ftake 'mexpt a b) '$zerob 0 1)))

    ;; Fallback for non-extended reals
    ((and (freeofl a *extended-reals*)
          (freeofl b *extended-reals*))
     (ftake 'mexpt a b))

    ;; Special cases
    ((and (eq a '$minf) (integerp b)) ;minf^integer
      (cond ((< b 0) 0)         ;minf^negative integer = 0
            ((eql 0 b) '$und)   ;minf^0 = und
            ((oddp b) '$minf)   ;minf^(odd positive) = minf
            ((evenp b) '$inf)   ;minf^(even positive) = inf
            (t '$und)))         ;shouldn't happen

    ((and (eq a '$minf) (alike1 b (div 1 2))) (mul '$%i '$inf))
    ((and (eq a '$ind) (integerp b) (> b 0)) ;ind^(positive integer)
     '$ind) ; ind^positive integer = ind

    ((and (eq a '$ind) (integerp b) (> 0 b)) ;ind^(negative integer)
     '$und) ; ind^negative integer = und

    ((and (eq a '$zeroa) (eq t (mgrp 0 b)))
     '$inf) ; zeroa^negative = inf

    ((and (eq a '$zeroa) (eq t (mgrp b 0)))
     '$zeroa) ; zeroa^positive = zeroa

    ((and (eq a '$zerob) (integerp b)) ;zerob^integer
     (simpab (mul (power -1 b) (power '$zeroa b))))

    ((and (eq a '$infinity) (eq t (mgrp b 0))) '$infinity) ; infinity^pos = infinity
    ((and (eq a '$inf) (eq t (mgrp b 0))) '$inf) ; inf^pos = infinity
    
    ((and (eql a -1) (eq b '$inf)) '$und) ; (-1)^inf = und
    ;; General fallback via exponentiation
    (t
     (let ((z (simpab (mul b (ftake '%log a)))))
    
       (cond
         ((eq z '$minf) 0)         ; exp(minf) = 0
         ((eq z '$zerob) 1)        ; exp(zerob) = 1
         ((eq z '$zeroa) 1)        ; exp(zeroa) = 1
         ((eq z '$ind) '$ind)      ; exp(ind) = ind
         ((eq z '$und) '$und)      ; exp(und) = und
         ((eq z '$inf) '$inf)      ; exp(inf) = inf
         ((eq z '$infinity) '$und) ; exp(infinity) = und
         (t (ftake 'mexpt a b)))))))) ; fall back

;; The hashtable *extended-real-eval* provides a mechanism for simplifying F(extended real); for
;; example log(inf) = inf and signum(zeroa) = 1.
(defvar *extended-real-eval* (make-hash-table :test #'equal))

(defmacro def-extended-real-evaluator (symbol args &body body)
  "Define a function for extended real evaluation and register it in *extended-real-eval*."
  `(progn
     (defun ,(intern (format nil "~A-OF-EXTENDED-REAL" symbol)) ,args
       ,@body)
     (setf (gethash ',symbol *extended-real-eval*)
           #',(intern (format nil "~A-OF-EXTENDED-REAL" symbol)))))

(def-extended-real-evaluator %log (e)
  (setq e (car e))
  (cond ((eq e '$minf) '$infinity)
        ((eq e '$zerob) '$infinity)
        ((eq e '$zeroa) '$minf)
        ((eq e '$ind) '$und) ;at this point, we don't know the sign of e, so I guess und is what we need
        ((eq e '$und) '$und)
        ((eq e '$inf) '$inf)
        ((eq e '$infinity) '$infinity)
        (t (ftake '%log e))))

;; The general simplifier handles signum(minf and inf), but here we define
;; signum for minf, zerob, zeroa, ind, and inf. We leave signum(infinity) a nounform.
(def-extended-real-evaluator %signum (e)
  (setq e (car e))
  (cond ((eq e '$minf) -1) ;signum(minf) = -1
        ((eq e '$zerob) -1)
        ((eq e '$zeroa) 1)
        ((eq e '$ind) '$ind)
        ((eq e '$und) '$und)
        ((eq e '$inf) 1)
        (t (ftake '%signum e))))

;; Extend erf to handle extended real inputs. The general simplifier handles
;; erf(minf) and erf(inf) OK. But this code extends erf to the five other 
;; extended real numbers.
(def-extended-real-evaluator %erf (e)
  (setq e (car e))
  (cond ((eq e '$minf) -1) ;erf(minf) = -1
        ((eq e '$zerob) '$zerob) ;erf(zerob) = zerob
        ((eq e '$zeroa) '$zeroa)  ;erf(zeroa) = zeroa
        ((eq e '$ind) '$ind) ;erf(ind) = ind
        ((eq e '$und) '$und) ;erf(und) = und
        ((eq e '$inf) 1)  ;erf(inf) = 1
        (t (ftake '%erf e))))

;; Apply the floor function to an extended real.
(def-extended-real-evaluator floor (e)
  (setq e (car e))
  (cond ((eq e '$minf) '$minf)
        ((eq e '$zerob) -1)
        ((eq e '$zeroa) 0)
        ((eq e '$ind) '$ind)
        ((eq e '$und) '$und)
        ((eq e '$inf) '$inf)
        (t (ftake '$floor e))))

(def-extended-real-evaluator realpart (e)
  (setq e (car e))
   (cond ((eq e '$minf) '$minf)
         ((eq e '$zerob) '$zerob)
         ((eq e '$zeroa) '$zeroa)
         ((eq e '$ind) '$ind)
         ((eq e '$und) '$und)
         ((eq e '$inf) '$inf)
         (t (ftake '%realpart e))))

(def-extended-real-evaluator imagpart (e)
  (setq e (car e))
   (cond ((eq e '$minf) 0)
         ((eq e '$zerob) 0)
         ((eq e '$zeroa) 0)
         ((eq e '$ind) '$ind) ;not sure
         ((eq e '$und) '$und)
         ((eq e '$inf) 0)
         (t (ftake '%imagpart e))))

(defun linearize-extended-real (e)
  "Partially do the extended real number arithmetic in the expression `e`. Specifically, if `e` is a 
  product, return either a Z or Z x extended real, where Z is finite; if `e` is exponential expression, 
  either return a finite expression or a extended-real; and if`e` has the form `F(X) attempt to return 
  either a finite expression or an extended real.

  For an expression such as `42 x inf`, this function does not simplify it to `inf`.  Such simplifications
  are done by the function `simpab`."
  (let ((fn (and (consp e) (gethash (mop e) *extended-real-eval*))))
    (cond
     ;; Early bailout: atomic or not free of extended reals, return `e`
     ((or ($mapatom e) (not (amongl *extended-reals* e))) e)
     ;; Multiplication of extended reals
     ((mtimesp e) (mul-extended (cdr e)))
     ;; Exponentiation involving extended reals
     ((mexptp e) (let ((preserve-direction t)) (mexpt-extended (second e) (third e))))
     ;; Known extended-real operator: apply simpab to args and dispatch fn
     (fn (funcall fn (mapcar #'simpab (cdr e))))
     ;; Subscripted function: recursively linearize subscripts and arguments
     (($subvarp (mop e))
      (subfunmake
       (subfunname e)
       (mapcar #'simpab (subfunsubs e))
       (mapcar #'simpab (subfunargs e))))
     ;; General fallback: apply operator of `e` to linearized args
     (t (fapply (caar e) (mapcar #'linearize-extended-real (cdr e)))))))

(defun simpab (e)
  ;; In the first stage, we attempt to linearize each term to the form either extended x finite
	;; or simply finite, where is one of Maxima's extended reals and finite is a product of non-extended reals.
	(let ((ee (linearize-extended-real e)))
	;; When the linearization is successful, we do additional simplifications on expressions that are
	;; affine in an extended real. We check for an affine expression using polynomialp.
	(cond (($polynomialp ee (fapply 'mlist *extended-reals*) 
	                       #'(lambda (q) (not (amongl *extended-reals* q)))
						   #'(lambda (q) (or (eql q 0) (eql q 1))))

        ;; Find the coefficients of each of the extended reals.
        (destructuring-bind (cf-minf cf-zerob cf-zeroa cf-ind cf-inf cf-infinity cf-und)
		                     (mapcar #'(lambda (q) (coeff ee q 1)) '($minf $zerob $zeroa $ind $inf $infinity $und))

       ;; When the coefficient of minf is negative, promote the minus infinity term to the infinity term
      (when (eq t (mgrp 0 cf-minf))
		     (setq cf-inf (sub cf-inf cf-minf)
                   cf-minf 0))

		  (when (eq t (mgrp 0 cf-inf))
		     (setq cf-minf (sub cf-minf cf-inf)
		           cf-inf 0))
          ;; Using the signs of the various coefficients, simplify
     
		  (cond 
        ((nonzero-p cf-und) '$und) ; und x anything + finite = und
        ;; inf + minf = und, inf + infinity = und, and minf + infinty = und.
				((and (nonzero-p cf-inf) (nonzero-p cf-minf)) '$und)
        ((and (nonzero-p cf-inf) (nonzero-p cf-infinity)) '$und)
        ((and (nonzero-p cf-minf) (nonzero-p cf-infinity)) '$und)
        ((nonzero-p cf-infinity) '$infinity) ; infinity x freeof und + finite = 

				;; Effectively, we convert a*inf + b*minf to (a-b)*inf
				((or (nonzero-p cf-inf) (nonzero-p cf-minf))
				 (let* ((cf (sub cf-inf cf-minf)) (sgn (maybe-asksign cf)));;; ($asksign cf)))
				 	(cond ((eq sgn '$neg) '$minf) ;negative x inf + finite = minf
					      ((eq sgn '$pos) '$inf)  ;pos x inf + finite = inf
						  ((eq sgn '$zero) '$und) ;zeroa x inf = und
						  ((eq sgn '$complex) '$infinity)
						  (t ee))))               ;give up
				((nonzero-p cf-ind) '$ind) ; finite x ind + freeof infinities and und = ind

				((or (nonzero-p cf-zerob) (nonzero-p cf-zeroa))
				  (cond (preserve-direction
				           (let* ((cf (sub cf-zeroa cf-zerob)) (sgn (maybe-asksign cf))) ;;;;(sgn ($asksign cf)))
				         	(cond ((eq sgn '$neg) (add '$zerob (ridofab ee))) ;negative x zeroa + finite = zerob + finite
					              ((eq sgn '$pos) (add '$zeroa (ridofab ee)))
						          (t ee))))
						(t (ridofab ee))))
				
				(t ee))))
		 (t ee))))

;; Redefine simpinf and infsimp to just call simpab followed by ridofab. 
(defun simpinf (e)
   (let (($simp t) (preserve-direction nil)) (ridofab (simpab e))))

(defun infsimp (e)
   (let (($simp t) (preserve-direction nil)) (ridofab (simpab e))))

(defun eq-ab (a b)
  (eql (ridofab a) (ridofab b)))

(defun add-extended-real (a b)
  (simpab `((mplus simp) ,a ,b)))

(defun $test_plus_comm ()
  (let ((L *extended-reals*) (bad nil))
    (dolist (a L)
      (dolist (b L)
        ;; test a + b = b + a
        (let ((ans1 (add-extended-real a b))
              (ans2 (add-extended-real b a)))
          (when (not (eq-ab ans1 ans2))
            (push (ftake 'mlist a b) bad)))))
  (fapply 'mlist bad)))


(defun $test_plus_assoc ()
  (let ((L *extended-reals*) (bad nil))
    (dolist (a L)
      (dolist (b L)
        (dolist (c L)
          ;; test a + (b + c) = (a + b) + c
          (let ((ans1 (add-extended-real a (add-extended-real b c)))
                (ans2 (add-extended-real (add-extended-real a b) c)))
            (when (not (eq-ab ans1 ans2))
              (push (ftake 'mlist a b c) bad))))))
  (fapply 'mlist bad)))


(defun $test_mult_comm ()
  (let ((L *extended-reals*)  (bad nil))
    (dolist (a L)
      (dolist (b L)
        ;; test a * b = b * a
        (let ((ans1 (mul-extended-real a b))
              (ans2 (mul-extended-real b a)))
          (when (not (eq-ab ans1 ans2))
            (push (ftake 'mlist a b) bad)))))
  (fapply 'mlist bad)))


(defun $test_mult_assoc ()
  (let ((L *extended-reals*) (bad nil))
    (dolist (a L)
      (dolist (b L)
        (dolist (c L)
          ;; test a * (b * c) = (a * b) * c
          (let ((ans1 (mul-extended-real a (mul-extended-real b c)))
                (ans2 (mul-extended-real (mul-extended-real a b) c)))
            (when (not (eq-ab ans1 ans2))
              (push (ftake 'mlist a b c) bad))))))
  (fapply 'mlist bad)))


(defun $test_distributivity ()
  (let ((L *extended-reals*) (bad nil))
    (dolist (a L)
      (dolist (b L)
        (dolist (c L)
          ;; test a * (b + c) = a*b + a*c
          (let ((ans1 (mul-extended-real a (add-extended-real b c)))
                (ans2 (add-extended-real
                       (mul-extended-real a b)
                       (mul-extended-real a c))))
            (when (not (eq-ab ans1 ans2))
              (push (ftake 'mlist a b c) bad))))))
  (fapply 'mlist bad)))
