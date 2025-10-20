;;; Copyright (c) Barton Willis 2023, 2025

;;; GNU GENERAL PUBLIC LICENSE Version 3, 29 June 2007
;;; For details, see the file LICENSE

#|  Maxima's general simplifier is responsible for simplifying inf - inf to 0.  This code doesn't fix
    this bugs, but it does allow arithmetic on the seven extended reals (minf, zerob, zeroa, ind, und, 
    inf, and infinity) to be done correctly. The one-argument limit function is the only 
    user-interface to this code; for example, limit(ind^2 + %pi) = ind and limit(inf^2 + zerob) = inf.

    Addition and multiplication extended real numbers is commutative and associative, but not distributive.
    The 54 violations to distributivity are given by the following list of lists. The first list
    member represents minf*(minf + zerob) = minf * minf = inf, but minf * minf + minf * zerob = inf + und = und.
     
    Unfortunately, at the top level of `limit` there is a call to expand(XXX,1,0) to the input XXX.  So 
    limit(minf*(minf + zerob)) is effectively limit(minf*minf + minf*zerob)= und, not inf as it should be.

[[minf, minf, zerob], [minf, minf, zeroa], [minf, minf, ind],
[minf, zerob, minf], [minf, zerob, inf], [minf, zerob, infinity],
[minf, zeroa, minf], [minf, zeroa, inf], [minf, zeroa, infinity],
[minf, ind, minf], [minf, ind, inf], [minf, ind, infinity],
[minf, inf, zerob], [minf, inf, zeroa], [minf, inf, ind],
[minf, infinity, zerob], [minf, infinity, zeroa], [minf, infinity, ind],
[inf, minf, zerob], [inf, minf, zeroa], [inf, minf, ind], [inf, zerob, minf],
[inf, zerob, inf], [inf, zerob, infinity], [inf, zeroa, minf],
[inf, zeroa, inf], [inf, zeroa, infinity], [inf, ind, minf], [inf, ind, inf],
[inf, ind, infinity], [inf, inf, zerob], [inf, inf, zeroa], [inf, inf, ind],
[inf, infinity, zerob], [inf, infinity, zeroa], [inf, infinity, ind],
[infinity, minf, zerob], [infinity, minf, zeroa], [infinity, minf, ind],
[infinity, zerob, minf], [infinity, zerob, inf], [infinity, zerob, infinity],
[infinity, zeroa, minf], [infinity, zeroa, inf], [infinity, zeroa, infinity],
[infinity, ind, minf], [infinity, ind, inf], [infinity, ind, infinity],
[infinity, inf, zerob], [infinity, inf, zeroa], [infinity, inf, ind],
[infinity, infinity, zerob], [infinity, infinity, zeroa],
[infinity, infinity, ind]]

|#

(in-package :maxima)

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
;; in 54 cases. For example, inf*(inf + zeroa) = inf, but inf * inf + inf * zeroa = und.
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
             (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x)))  ;set ans to the complex sign of x
             (cond ((eq sgn '$neg) '$inf)
                   ((eq sgn '$pos) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((eq sgn '$complex) '$infinity)
                   (t (mul x l))))

          ((eq l '$inf)
             (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x)))  ;set ans to the complex sign of x
             (cond ((eq sgn '$neg) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((eq sgn '$pos) '$inf)
                   ((eq sgn '$complex) '$infinity)
                   (t (mul x l))))

          ((eq l '$zerob)
           (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x)))  ;set ans to the complex sign of x
             (cond ((or (eq sgn '$neg) (eq sgn '$nz)) '$zeroa)
                   ((eq sgn '$zero) 0)
                   ((or (eq sgn '$pos) (eq sgn '$pz)) '$zerob)
                   (t (mul x l))))
                   
           ((eq l '$zeroa)
           (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x)))  ;set ans to the complex sign of x
             (cond ((or (eq sgn '$neg) (eq sgn '$nz)) '$zerob)
                   ((eq sgn '$zero) 0)
                   ((or (eq sgn '$pos) (eq sgn '$pz)) '$zeroa)
                   (t (mul x l))))

          ((eq l '$ind) 
             (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x))) ;set ans to the complex sign of x
             (if (eq sgn '$zero) 0 '$ind))

          ((eq l '$infinity) ;0*infinity = und & X*infinity = infinity.
             (setq sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x)))  ;set ans to the complex sign of x
             (if (eq sgn '$zero) '$und '$infinity))

          ((eq l '$und) '$und)
          (t (mul x l)))))

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

(defun mexpt-extended (a b)
  (setq a (my-infsimp a))
  (setq b (my-infsimp b))
  (cond
    ;; Lookup in table
    ((gethash (list a b) *extended-real-mexpt-table* nil))

    ;; Fallback for non-extended reals
    ((and (not (member a *extended-reals*))
          (not (member b *extended-reals*)))
     (ftake 'mexpt a b))

    ;; Special cases
    ((and (eq a '$minf) (integerp b) (< b 0))
     0) ; minf^negative integer = 0

    ((and (eq a '$ind) (integerp b) (> b 0))
     '$ind) ; ind^positive integer = ind

    ((and (eq a '$ind) (integerp b) (> 0 b))
     '$und) ; ind^negative integer = und

    ((and (eq a '$zeroa) (eq t (mgrp 0 b)))
     '$inf) ; zeroa^negative = inf

    ((and (eq a '$zeroa) (eq t (mgrp b 0)))
     '$zeroa) ; zeroa^positive = zeroa

    ((and (eq a '$zerob) (integerp b))
     (my-infsimp (mul (power -1 b)
                      (power '$zeroa b))))

    ;; General fallback via exponentiation
    (t
     (let ((z (my-infsimp (mul b (ftake '%log a)))))
       (cond
         ((eq z '$minf) 0)         ; exp(minf) = 0
         ((eq z '$zerob) 1)        ; exp(zerob) = 1
         ((eq z '$zeroa) 1)        ; exp(zeroa) = 1
         ((eq z '$ind) '$ind)      ; exp(ind) = ind
         ((eq z '$und) '$und)      ; exp(und) = und
         ((eq z '$inf) '$inf)      ; exp(inf) = inf
         ((eq z '$infinity) '$und) ; exp(infinity) = und
         (t (ftake 'mexpt a b))))))) ; fall back
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

;; The general simplifier handles signum(minf and inf), but here we define
;; signum for minf, zerob, zeroa, ind, and inf. We leave signum(infinity) a nounform.
(defun signum-of-extended-real (e)
  (setq e (car e))
  (cond ((eq e '$minf) -1) ;signum(minf) = -1
        ((eq e '$zerob) -1)
        ((eq e '$zeroa) 1)
        ((eq e '$ind) '$ind)
        ((eq e '$und) '$und)
        ((eq e '$inf) 1)
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

(defun my-infsimp (e)
  (let ((fn (if (consp e) (gethash (mop e) *extended-real-eval*) nil)))
   (cond ((or ($mapatom e) (not (amongl *extended-reals* e))) e) ;early bailout might boost speed
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
           (fapply (caar e) (mapcar #'my-infsimp (cdr e)))))))

;; Redefine simpinf, infsimp, and simpab to just call my-infsimp. 
(defun simpab (e) 
  (my-infsimp e))

(defun simpinf (e)
   (ridofab (simpab e)))

(defun infsimp (e)
   (ridofab (simpab e)))
