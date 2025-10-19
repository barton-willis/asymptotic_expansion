;;; Copyright (c) Barton Willis 2023

;;; GNU GENERAL PUBLIC LICENSE Version 3, 29 June 2007
;;; For details, see the file LICENSE

(in-package :maxima)

(declare-top (special origval
		      *indicator numer denom exp var val
		      taylored logcombed
		      $exponentialize lhp? lhcount
		      loginprod? a context limit-assumptions
		      limit-top))
;; This is a start at an extension of the function asksign. It allows responding
;; that the sign is anyone of neg, nz, zero, pz, pos, pnz, imaginary, or complex.   
;; When a user inputs a sign and it is either  neg, nz, zero, pz, or pos the 
;; function does an appropriate assume. When a user input is either complex or 
;; imaginary, it does an appropriate declare.
(defmfun $askcsign (e &optional (learn nil))
  ;;(setq e (ridofab e)) ;; not sure about this!
  (let ((sgn ($csign e)) (*standard-output* *debug-io*)
        (allowed (list '$neg '$nz '$zero '$pz '$pos '$imaginary '$complex)))
    (when (not (member sgn allowed))
           (mtell "csign(~M) = " e)
           (setq sgn ($read))
           ;(mtell "~%")
           (while (not (member sgn allowed))
              (mtell "sign must be one of ~M ~%" (fapply 'mlist allowed))
              (setq sgn ($read)))
          (when learn
            (cond ((eq sgn '$neg)
                      (assume (ftake 'mlessp e 0)))
                  ((eq sgn '$nz)
                      (assume (ftake 'mleqp e 0)))
                  ((eq sgn '$zero)
                      (assume (ftake '$equal e 0)))
                  ((eq sgn '$pz)
                      (assume (ftake 'mgeqp e 0)))
                  ((eq sgn '$pos)
                      (assume (ftake 'mgreaterp e 0)))
                  ((and (eq sgn '$complex) (atom e))
                      (mfuncall '$declare e '$complex))
                  ((and (eq sgn '$imaginary) (atom e))
                      (mfuncall '$declare e '$imaginary)))))
    sgn))

(defun extended-real-p (e)
  "Return true if `e` is a symbol and an element of *extended-reals*. The seven extended
   reals are `minf`, `zerob`, `zeroa`, `ind`, `inf`, `infinity`, and `und`."
  (and (symbolp e) (member e *extended-reals*)))

;; We use a hashtable to represent the addition table for extended real numbers.
;; Arguably, a hashtable isn't the most compact representation, but this scheme
;; is easy to extend and modify.

;; When the sum of two extended reals is undefined (for example, minf + inf),
;; we omit the entry from the hashtable. In such cases, the function add-extended-real
;; returns 'und'.

;; Possibly controversial: since limit ((x, y) -> (0⁺, 0⁻)) of (x + y) equals 0,
;; we define zerob + zeroa = 0. The four non-associative cases are:
;; +(zerob, zerob, zeroa), +(zerob, zeroa, zeroa), +(zeroa, zerob, zerob),and +(zeroa, zeroa, zerob).
(defvar *extended-real-add-table* (make-hash-table :test #'equal))

(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-add-table*) (third a)))
   (list (list '$minf '$minf '$minf)
         (list '$minf '$zerob '$minf)
         (list '$minf '$zeroa '$minf)
         (list '$minf '$ind '$minf)

         (list '$zerob '$zerob '$zerob)
         (list '$zerob '$zeroa 0) ; possibly controversial
         (list '$zeroa '$zeroa '$zeroa)

         (list '$inf '$inf '$inf)
         (list '$inf '$zerob '$inf)
         (list '$inf '$zeroa '$inf)
         (list '$inf '$ind '$inf)

         (list '$infinity '$zerob '$infinity)
         (list '$infinity '$zeroa '$infinity)
         (list '$infinity '$ind '$infinity)

         (list '$ind '$ind '$ind)
         (list '$ind '$zerob '$ind)
         (list '$ind '$zeroa '$ind)))

;; Add extended reals a & b. When (a,b) isn't a key in the hashtable, return
;; $und. The table is symmetric, if looking up (a,b) fails, we look for (b,a).
(defun add-extended-real(a b)
  (gethash (list a b) *extended-real-add-table* 
    (gethash (list b a) *extended-real-add-table* '$und)))

(defun add-expr-infinities (x l)
  "Add the members of the list of extended reals l, then add to the list of finite expressions `x`."
   (let ((lsum (cond ((null l) 0)
                     ((null (cdr l)) (car l))
                     (t (reduce #'add-extended-real l)))))
  (if (zerop2 lsum)
      (fapply 'mplus x)
      lsum))) ; x + minf = minf, x + ind = ind, x + und = und, x + inf = inf, x + infinity = infinity.
 
 ;; Add a list of expressions, including extended reals. When the optional
;; argument flag is true, dispatch infsimp on each list member before adding.
(defun addn-extended (l)
  (let ((xterms nil) (rterms nil))
    (dolist (lk l)
      (setq lk (my-infsimp lk))
      (if (extended-real-p lk) (push lk xterms) (push lk rterms)))
    (add-expr-infinities rterms xterms)))      

;; We use a hashtable to represent the multiplication table for extended
;; real numbers. The table is symmetric, so we list only its "upper" half.
;; When a value isn't found in the hashtable, mult-extended-real returns `und`,
;; so we omit entries for those cases.

;; This multiplication is commutative and associative, but distributivity fails
;; in 56 cases. For example, inf*(inf + zeroa) = inf, but inf * inf + inf * zeroa = und.
(defvar *extended-real-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mult-table*) (third a)))
   (list (list '$minf '$minf '$inf)
         (list '$minf '$inf '$minf)
         (list '$minf '$infinity '$infinity)

         (list '$zerob '$zerob '$zeroa)
         (list '$zerob '$ind 0)
         (list '$zeroa '$ind 0)
         (list '$zerob '$zeroa '$zerob)
         (list '$zeroa '$zeroa '$zeroa)
         
         (list '$inf '$inf '$inf)
         (list '$inf '$infinity '$infinity)

         (list '$infinity '$infinity '$infinity)

         (list '$ind '$ind '$ind)))

;; Multiply extended reals a & b. When (a,b) isn't a key in the hashtable, return
;; $und. The table is symmetric, so we look for both (a,b) and if that fails,
;; we look for (b,a).
(defun mult-extended-real (a b)
  (gethash (list a b) *extended-real-mult-table* 
	    (gethash (list b a) *extended-real-mult-table* '$und)))

(defun muln-extended (l)
  (let ((xterms nil) (rterms 1))
    (dolist (lk l)
      (setq lk (my-infsimp lk))
      (if (extended-real-p lk) (push lk xterms) (setq rterms (mul lk rterms))))
    (mult-expr-infinities rterms xterms)))      

(defun nounform-mult (a b)
  "Return simplified noun-form product of a and b without dispatching the simplifier."
  (cons (list 'mtimes 'simp) (sort (list a b) '$orderlessp)))

;; At one time, product (sum (f(i), i, 1, inf), j, 1, inf) produced an infinite loop.
;; To fix it, I changed the code to only call csign when it was needed--before
;; the call to csign was in the let. I don't know why this fixed the bug, but 
;; it did.

(defun mult-expr-infinities (x l) 

  (let ((sgn))
    (setq l (cond ((null l) 1)
                  ((null (cdr l)) (car l))
                  (t (reduce #'mult-extended-real l))))
            
    (cond 
      ((eql l 1) x) ;X*1 = X
      ((eql l 0) 0) ;X*0 = 0
      ((eq l '$minf)
             (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x)))  ;set ans to the complex sign of x
             (cond ((eq sgn '$neg) '$inf)
                   ((eq sgn '$pos) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((or (eq sgn '$complex) (eq sgn '$imaginary)) '$infinity)
                   (t (nounform-mult x l))))

          ((eq l '$inf)
             (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x)))  ;set ans to the complex sign of x
             (cond ((eq sgn '$neg) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((eq sgn '$pos) '$inf)
                   ((or (eq sgn '$complex) (eq sgn '$imaginary)) '$infinity)
                   (t (nounform-mult x l))))

          ((eq l '$zerob)
           (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x)))  ;set ans to the complex sign of x
             (cond ((or (eq sgn '$neg) (eq sgn '$nz)) '$zeroa)
                   ((eq sgn '$zero) 0)
                   ((or (eq sgn '$pos) (eq sgn '$pz)) '$zerob)
                   (t (nounform-mult x l))))
                   
           ((eq l '$zeroa)
           (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x)))  ;set ans to the complex sign of x
             (cond ((or (eq sgn '$neg) (eq sgn '$nz)) '$zerob)
                   ((eq sgn '$zero) 0)
                   ((or (eq sgn '$pos) (eq sgn '$pz)) '$zeroa)
                   (t (nounform-mult x l))))

          ((eq l '$ind) 
             (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x))) ;set ans to the complex sign of x
             (if (eq sgn '$zero) 0 '$ind))

          ((eq l '$infinity) ;0*infinity = und & X*infinity = infinity.
             (setq sgn (if *getsignl-asksign-ok* ($askcsign x t) ($csign x)))  ;set ans to the complex sign of x
             (if (eq sgn '$zero) '$und '$infinity))

          ((eq l '$und) '$und)
          (t (nounform-mult x l)))))

(defvar *extended-real-mexpt-table* (make-hash-table :test #'equal))

(mapcar #'(lambda (a) 
  (setf (gethash (list (first a) (second a)) *extended-real-mexpt-table*) (third a)))
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
   (list '$zerob '$ind '$ind) 
   (list '$zerob '$inf 0) 
   (list '$zerob '$infinity 0) 
   (list '$zerob '$und '$und) 
   
   (list '$zeroa '$minf '$und) 
   (list '$zeroa '$zerob '$und) 
   (list '$zeroa '$zeroa '$und) 
   (list '$zeroa '$ind '$ind) 
   (list '$zeroa '$inf 0) 
   (list '$zeroa '$infinity 0)
   (list '$zeroa '$und '$und) 
   
   (list '$ind '$minf '$und) 
   (list '$ind '$zerob '$und) 
   (list '$ind '$zeroa '$und) 
   (list '$ind '$ind '$und) 
   (list '$ind '$inf '$und) 
   (list '$ind '$infinity '$und) 
   (list '$ind '$und '$und) 

   (list '$inf '$minf 0) 
   (list '$inf '$zerob '$und) 
   (list '$inf '$zeroa '$und) 
   (list '$inf '$ind '$und) 
   (list '$inf '$inf '$inf) 
   (list '$inf '$infinity '$infinity)
   (list '$inf '$und '$und)

   (list '$infinity '$minf '$infinity)
   (list '$infinity '$zerob 1) 
   (list '$infinity '$zeroa 1) 
   (list '$infinity '$ind '$und) 
   (list '$infinity '$inf '$infinity) 
   (list '$infinity '$infinity '$infinity)
   (list '$infinity '$und '$und) 

   (list '$und '$minf '$und) 
   (list '$und '$zerob '$und) 
   (list '$und '$zeroa '$und) 
   (list '$und '$ind '$und) 
   (list '$und '$inf '$und) 
   (list '$und '$infinity '$und) 
   (list '$und '$und '$und)))

;; missing: (-2)^minf = 0, (-2)^ind = ?, (-2)^infinity = und(?), (-1)^infinity = und(?), 2^infinity = und?
;; 2^ind = ind, (-1)^ind = und(?), (-1)^minf = und (?)
(defvar *missing* nil)
(defun mexpt-extended (a b)
  (setq a (my-infsimp a))
  (setq b (my-infsimp b))
  (let ((amag) (sgn))

  (cond ((gethash (list a b) *extended-real-mexpt-table* nil)) ;look up
        ((and (not (member a *extended-reals*)) (not (member b *extended-reals*)))
          (ftake 'mexpt a b))
        ;; a^inf 
        ((eq b '$inf)
          (setq amag ($cabs a))
          (cond ((eq t (mgrp 1 amag)) 0); (inside unit circle)^inf = 0
                ((and (eq t (mgrp amag 1)) (manifestly-real-p a)) '$inf) ;outside unit circle^inf = inf
                ((eql 1 a) '$und) ; 1^inf = und
                ((eql 1 amag) '$ind) ; (on unit circle and not 1)^inf = ind
                ((eq t (mgrp amag 1)) '$infinity) ;outside unit circle^inf = infinity
                (t (ftake 'mexpt a b))))
        ((and (eq a '$ind) (integerp b) (> b 0)) ;ind^positive integer = $ind
          '$ind)

        ((and (eq a '$ind) (integerp b) (> 0 b)) ;ind^negative integer = $und
          '$und)

        ;; For inf^x, do an asksign on realpart(x)
        ((eq a '$inf)
          (setq sgn ($asksign ($realpart b)))
          (cond ((eq sgn '$neg) '$zeroa)
                ((eq sgn '$pos) '$inf)
                ((eq sgn '$zero) '$und)
                (t '$und)))

         ;; For infinity^x, do an asksign on realpart(x)
        ((eq a '$infinity)
          (setq sgn ($asksign ($realpart b)))
          (cond ((eq sgn '$neg) '$zeroa)
                ((eq sgn '$pos) '$infinity)
                ((eq sgn '$zero) '$und)
                (t '$und)))
        ;; This needs some work.
        ((eq a '$minf)
          (mul (power -1 b) (mexpt-extended '$inf b)))

        ;;(x>1)^minf = 0
        ((and (eq b '$minf) (eq t (mgrp a 1))) 0)

        ;; (0 < x < 1)^minf = inf
        ((and (eq b '$minf) (eq t (mgrp 0 a)) (eq t (mgrp a 1))) '$inf)

        ((and (eq a '$zeroa) (eq t (mgrp 0 b))) ; zeroa^negative = inf
          '$inf)
        
        ((and (eq a '$zeroa) (eq t (mgrp b 0))) ; zeroa^pos = zeroa
          '$zeroa)

        ((and (eq a '$zerob) (integerp b))
         (my-infsimp (mul (power -1 b) (power '$zeroa b))))

        (t 
         (push (ftake 'mlist a b) *missing*)
        (ftake 'mexpt a b)))))

;; The functions $infsimp, $mul, and $add are only intended for testing
(defun $infsimp (e)
   (my-infsimp (ratdisrep e)))

(defun $mul (&rest a)
   (muln-extended (mapcar #'ratdisrep a)))

(defun $add (&rest a)
   (addn-extended (mapcar #'ratdisrep a)))

(defun $power (a b)
   (mexpt-extended (ratdisrep a) (ratdisrep b)))

(defvar *extended-real-eval* (make-hash-table :test #'equal))

(defun log-of-extended-real (e)
  (setq e (car e))
  (cond ((eq e '$minf) '$infinity)
        ((eq e '$zerob) '$infinity)
        ((eq e '$zeroa) '$minf)
        ((eq e '$ind) '$und) ;could look to see if e is nonzero?
        ((eq e '$und) '$und)
        ((eq e '$inf) '$inf)
        ((eq e '$infinity) '$infinity)
        (t (ftake '%log e))))
(setf (gethash '%log *extended-real-eval*) #'log-of-extended-real)

;; The general simplifier handles signum(minf and inf), so we'll define
;; signum for each of the seven extended real numbers. Maybe 
;; signum(infinity) = ind is OK, but I'm not sure.
(defun signum-of-extended-real (e)
  (setq e (car e))
  (cond ((eq e '$minf) -1) ;signum(minf) = -1
        ((eq e '$zerob) -1)
        ((eq e '$zeroa) 1)
        ((eq e '$ind) '$ind)
        ((eq e '$und) '$und)
        ((eq e '$inf) 1)
        ((eq e '$infinity) '$ind) ; not sure
        (t (ftake '%signum e))))
(setf (gethash '%signum *extended-real-eval*) #'signum-of-extended-real)

;; Extend erf to handle extended real inputs. The general simplifier handles
;; erf(minf) and erf(inf) OK. But this code extends erf to the five other 
;; extended real numbers.
(defun erf-of-extended-real (e)
  (setq e (car e))
  (cond ((eq e '$minf) -1) ;erf(minf) = -1
        ((eq e '$zerob) '$zerob) ;erf(zerob) = zerob
        ((eq e '$zeroa) '$zeroa)  ;erf(zeroa) = zeroa
        ((eq e '$ind) '$ind) ;erf(ind) = ind
        ((eq e '$und) '$und) ;erf(und) = und
        ((eq e '$inf) 1)  ;erf(inf) = 1
        ((eq e '$infinity) '$infinity)  ;erf(infinity) = infinity (not sure)
        (t (ftake '%erf e))))
(setf (gethash '%erf *extended-real-eval*) #'erf-of-extended-real)

;; Apply the floor function to an extended real.
(defun floor-of-extended-real (e)
  (setq e (car e))
  (cond ((eq e '$minf) '$minf)
        ((eq e '$zerob) -1)
        ((eq e '$zeroa) 0)
        ((eq e '$ind) '$ind)
        ((eq e '$und) '$und)
        ((eq e '$inf) '$inf)
        ((eq e '$infinity) '$und) ; not sure
        (t (ftake '$floor e))))
(setf (gethash '$floor *extended-real-eval*) #'floor-of-extended-real)

(defun realpart-of-extended-real (e)
  (setq e (car e))
   (cond ((eq e '$minf) '$minf)
         ((eq e '$zerob) '$zerob)
         ((eq e '$zeroa) '$zeroa)
         ((eq e '$ind) '$ind)
         ((eq e '$und) '$und)
         ((eq e '$inf) '$inf)
         ((eq e '$infinity) '$und) ; not sure
         (t (ftake '%realpart e))))
(setf (gethash '%realpart *extended-real-eval*) #'realpart-of-extended-real)

(defun imagpart-of-extended-real (e)
  (setq e (car e))
   (cond ((eq e '$minf) 0)
         ((eq e '$zerob) 0)
         ((eq e '$zeroa) 0)
         ((eq e '$ind) '$ind) ;not sure
         ((eq e '$und) '$und)
         ((eq e '$inf) 0)
         ((eq e '$infinity) '$und) ; not sure
         (t (ftake '%imagpart e))))
(setf (gethash '%imagpart *extended-real-eval*) #'imagpart-of-extended-real)

;; I'm not sure what else this might do? I suppose sum(inf,k,a,b) =
;; inf when a < b would be OK. For now, it does nothing.
(defun sum-of-extended-real (e)
  (fapply '%sum e))
(setf (gethash '%sum *extended-real-eval*) #'sum-of-extended-real)

;; The calculation 

;;  xxx : product(f(i),i,1,inf);
;;  xxx : subst(f(i) = product(g(k),k,1,inf), xxx);
;;  xxx : subst(g(k) = product(w(m),m,1,inf), xxx);

;; finishes, but is very slow and it calls infsimp many times. The
;; calculation with standard Maxima is also slow.

;; {ceiling, f, g, acos, asin, asinh, atan, cos, derivative,
;;  expintegral_ei, gamma, gamma_incomplete, integrate, limit, sin, zeta}

;; For code development, collect all expressions that don't have a 
;; function for extending them to the extended real numbers.
(defvar *missinginfsimp* nil)
(defun my-infsimp (e)
  (let ((fn (if (consp e) (gethash (mop e) *extended-real-eval*) nil)))
   (cond (($mapatom e) e)
         ((mplusp e) (addn-extended (cdr e)))
         ((mtimesp e) (muln-extended (cdr e)))
         ((mexptp e) (mexpt-extended (second e) (third e)))
         ;; The operator of e has an infsimp routine, so map my-infsimp over 
         ;; the arguments of e and dispatch fn.
         (fn (funcall fn (mapcar #'my-infsimp (cdr e))))
         ;; Eventually, we should define a function for the polylogarithm functions.
         ;; But running the testsuite doesn't catch any cases such as li[2](ind).
         (($subvarp (mop e)) ;subscripted function
		      (subfunmake 
		      (subfunname e) 
			        (mapcar #'my-infsimp (subfunsubs e)) 
			        (mapcar #'my-infsimp (subfunargs e))))
         (t 
           ;(when (amongl '($minf $zerob $zeroa $ind $und $inf $infinity) e)
            ;  (push (caar e) *missinginfsimp*))
           (fapply (caar e) (mapcar #'my-infsimp (cdr e)))))))

;; Redefine simpinf, infsimp, and simpab to just call my-infsimp. 
(defun simpab (e) 
  (my-infsimp e))

(defun simpinf (e)
   (ridofab (simpab e)))

(defun infsimp (e)
   (ridofab (simpab e)))
