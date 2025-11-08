;;; Copyright (c) Barton Willis 2023, 2025

;;; GNU GENERAL PUBLIC LICENSE Version 3, 29 June 2007
;;; For details, see the file LICENSE

#|  
Maxima’s general simplifier is responsible for incorrectly simplifying inf - inf to 0, 0*inf to 0, and .... 
This code does not fix these bugs, but it does rework the Maxima functions simpfinf, infsimp, and simpab.
The one-argument limit function is the sole user interface to this code. For example, limit(ind^2 + %pi) 
evaluates to ind, and limit(inf^2 + zerob) evaluates to inf. 

This code has three functions for internal use. They are simpinf, infsimp, and simpab. The main function is 
simpab. The identical functions simpinf and infsimp call simpab followed by setting both
zeroa and zerob to zero. 

Addition and multiplication of extended real numbers are commutative and associative. This assumes that
zerob+zeroa = 0.

There are 62 violations of distributivity, illustrated by the following list of lists. The first entry represents 
the expression infinity*(infinity + ind), which simplifies to infinity*infinity = infinity. However, distributing 
yields infinity^2 + infinity*ind = infinity + und = und.

Unfortunately, at the top level of limit, Maxima calls expand(XXX, 1, 0) on the input XXX. As a result, 
limit(minf*(minf + zerob)) is effectively evaluated as limit(minf*minf + minf*zerob) = und, rather than 
the correct value inf.

[[infinity, infinity, ind], [infinity, infinity, zeroa],
[infinity, infinity, zerob], [infinity, inf, inf], [infinity, inf, ind],
[infinity, inf, zeroa], [infinity, inf, zerob], [infinity, ind, infinity],
[infinity, ind, inf], [infinity, ind, minf], [infinity, zeroa, infinity],
[infinity, zeroa, inf], [infinity, zeroa, minf], [infinity, zerob, infinity],
[infinity, zerob, inf], [infinity, zerob, minf], [infinity, minf, ind],
[infinity, minf, zeroa], [infinity, minf, zerob], [infinity, minf, minf],
[inf, infinity, ind], [inf, infinity, zeroa], [inf, infinity, zerob],
[inf, inf, ind], [inf, inf, zeroa], [inf, inf, zerob], [inf, ind, infinity],
[inf, ind, inf], [inf, ind, minf], [inf, zeroa, infinity], [inf, zeroa, inf],
[inf, zeroa, minf], [inf, zerob, infinity], [inf, zerob, inf],
[inf, zerob, minf], [inf, minf, ind], [inf, minf, zeroa], [inf, minf, zerob],
[ind, zeroa, zerob], [ind, zerob, zeroa], [zeroa, zeroa, zerob],
[zeroa, zerob, zeroa], [zerob, zeroa, zerob], [zerob, zerob, zeroa],
[minf, infinity, ind], [minf, infinity, zeroa], [minf, infinity, zerob],
[minf, inf, ind], [minf, inf, zeroa], [minf, inf, zerob],
[minf, ind, infinity], [minf, ind, inf], [minf, ind, minf],
[minf, zeroa, infinity], [minf, zeroa, inf], [minf, zeroa, minf],
[minf, zerob, infinity], [minf, zerob, inf], [minf, zerob, minf],
[minf, minf, ind], [minf, minf, zeroa], [minf, minf, zerob]]

Testsuite: Causes one asksign involving a gensym running rtest_simplify_sum.mac. 
These failures are not semantic:

Error summary:
Error(s) found:
   rtest_sqrt.mac problem:    (9)
   rtest_limit.mac problems:    (201 232)
   rtest_trace.mac problem:    (87)
   rtest_limit_extra.mac problem:    (94)

Tests that were expected to fail but passed:
   rtest_limit_extra.mac problems:    (125 126 127 267)
 
5 tests failed out of 19,366 total tests.


Specifically these failures are:

********************* rtest_sqrt.mac: Problem 9 (line 45) *********************

Input:
limit([sqrt(inf), sqrt(- inf), sqrt(minf), sqrt(- minf), sqrt(infinity)])

Result:
[inf, %i inf, und, inf, infinity]

This differed from the expected result:
[inf, infinity, infinity, inf, infinity]

******************* rtest_limit.mac: Problem 201 (line 762) *******************

Input:
limit(ind inf)

Result:
und

This differed from the expected result:
ind inf

******************* rtest_limit.mac: Problem 232 (line 877) *******************

Input:
        1/x
limit((x    - 1) sqrt(x), x, 0, minus)

Result:
%i inf

This differed from the expected result:
infinity

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

(defun extended-real-p (e)
  "Return true if `e` is a symbol and an element of *extended-reals*. The seven extended
   reals are `minf`, `zerob`, `zeroa`, `ind`, `inf`, `infinity`, and `und`."
  (and (symbolp e) (member e *extended-reals*)))

;; We use a hashtable to represent the addition table for extended real numbers.
;; Arguably, a hashtable isn't the most compact representation, but this scheme
;; is easy to extend and modify.

;; The hashtable automatically extends by commutativity--so if a key (a,b) isn't in the 
;; table, the addition code automatically looks for the key (b,a). If both keys
;; (a,b) and (b, a) are missing, the function add-extended-real returns 'und'.

;; If zeroa + zerob = und, then integrate(tan(x)^(1/3)/(cos(x)+sin(x))^2,x,0,%pi/2) yields a nounform,
;; but if zeroa + zerob=0, we get the correct value for this definite integral. But notice that
;; defining zeroa + zerob = 0, breaks the closure of addition on the set of extended reals. The
;; function add-extended-real needs additional logic when addition isn't closed on the set of
;; extended reals.
(defvar *extended-real-add-table* (make-hash-table :test #'equal))

(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-add-table*) (third a)))
   (list (list '$minf '$minf '$minf)
         (list '$minf '$zerob '$minf)
         (list '$minf '$zeroa '$minf)
         (list '$minf '$ind '$minf)

         (list '$zerob '$zerob '$zerob)
         (list '$zerob '$zeroa 0) ; controversial--let's make zerob+zeroa -> 0
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
;; When both keys (a,b) & (b,a) aren't in the table, return und.
(defun add-extended-real (a b)
  (cond ((eql 0 a) b)
        ((eql 0 b) a)
        (t
            (gethash (list a b) *extended-real-add-table* 
              (gethash (list b a) *extended-real-add-table* '$und)))))

(defun add-expr-infinities (x l)
  "Add the members of the list of extended reals l, then add to the list of finite expressions `x`."
   (let ((lsum (cond ((null l) 0)
                     ((null (cdr l)) (car l))
                     (t (reduce #'add-extended-real l)))))
  (if (zerop2 lsum)
      (fapply 'mplus x)
      lsum))) ; x + minf = minf, x + ind = ind, x + und = und, x + inf = inf, x + infinity = infinity.
 
 (defun addn-extended (l)
 "Add a list of expressions `l`, including extended reals. Dispatch `simpab` on each term before adding."
  (let ((xterms nil) (rterms nil))
    (dolist (lk l)
      (setq lk (simpab lk))
      (if (extended-real-p lk) (push lk xterms) (push lk rterms)))
    (add-expr-infinities rterms xterms)))      

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
         (list '$zerob '$ind '$ind) ;maybe would be OK to define zeroa x ind = 0 & zerob x ind = 0
         (list '$zeroa '$ind '$ind)
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
      (setq lk (simpab lk))
      (if (extended-real-p lk) (push lk xterms) (setq rterms (mul lk rterms))))
    (mult-expr-infinities rterms xterms)))      

;; At one time, product (sum (f(i), i, 1, inf), j, 1, inf) produced an infinite loop.
;; To fix it, I changed the code to only call csign when it was needed--before
;; the call to csign was in the let. I don't know why this fixed the bug, but 
;; it did.
(defun mult-expr-infinities (x l)
  "Return x times the product of the members in the list l. The expression `x` should be free of extended
   real numbers, and `l` should be a CL list of extended reals."
  (let ((lprod (cond ((null l) 1)
                     ((null (cdr l)) (car l))
                     (t (reduce #'mult-extended-real l)))))
    (cond
      ((eql lprod 1) x) ; X*1 = X
      ((eql lprod 0) 0) ; X*0 = 0
      (t
       (let ((sgn (if *getsignl-asksign-ok* ($asksign x) ($csign x))))
         (cond
           ((eq lprod '$minf)
            (cond ((eq sgn '$neg) '$inf)          ;minf x neg = inf
                  ((eq sgn '$pos) '$minf)         ;minf x pos = minf
                  ((eq sgn '$zero) '$und)         ;minf x zero = und
                  ((eq sgn '$complex) '$infinity) ;minf x infinity = infinity
                  (t (mul x lprod))))             ;give up--nounform return

           ((eq lprod '$inf)
            (cond ((eq sgn '$neg) '$minf)         ;inf x neg = minf
                  ((eq sgn '$zero) '$und)         ;inf x zero = und
                  ((eq sgn '$pos) '$inf)          ;inf x pos = inf
                  ((eq sgn '$complex) '$infinity) ;inf x complex = infinity
                  (t (mul x lprod))))             ;give up--nounform return

           ((eq lprod '$zerob)
            (cond ((not preserve-direction) 0)
                  ((or (eq sgn '$neg) (eq sgn '$nz)) '$zeroa) ;zerob x {neg nz} = zeroa
                  ((eq sgn '$zero) 0)                         ;zerob x zero = 0
                  ((or (eq sgn '$pos) (eq sgn '$pz)) '$zerob) ;zerob x {pos,pz} = zerob
                  (t (mul x lprod))))                         ;give up--nounform return

           ((eq lprod '$zeroa)
            (cond ((not preserve-direction) 0)
                  ((or (eq sgn '$neg) (eq sgn '$nz)) '$zerob) ;zeroa x {neg nz} = zerob
                  ((eq sgn '$zero) 0)                         ;zeroa x zero = 0
                  ((or (eq sgn '$pos) (eq sgn '$pz)) '$zeroa) ;zeroa x {pos,pz} = zeroa
                  (t (mul x lprod))))                         ;give up--nounform return

           ((eq lprod '$ind)
            (if (eq sgn '$zero) 0 '$ind)) ; ind x zero = 0; otherwise ind

           ((eq lprod '$infinity) ; 0 x infinity = und; otherwise = infinity.
            (cond ((eq sgn '$zero) '$und) ; 0 x infinity = und
                  ((member sgn '($pos '$neg '$pn)) '$infinity) ;infinity x {pos, neg, pn} = infinity
                  (t '$und))) ; infinity x pnz = und

           ((eq lprod '$und) '$und) ;und x anything = und
           (t (mul x lprod))))))))  ;give up--nounform return
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

   (list '$infinity '$minf '$infinity) 
   ;(list '$infinity '$zerob 1) 
   ;(list '$infinity '$zeroa 1) 
   (list '$infinity '$inf '$infinity) 
   (list '$infinity '$infinity '$infinity)))

(defvar *missing* nil)
(defun mexpt-extended (a b)
  (setq a (simpab a))
  (setq b (simpab b))
  (cond
    ;; Lookup in table
    ((and
       (member a *extended-reals*)
       (member b *extended-reals*)
       (gethash (list a b) *extended-real-mexpt-table* '$und)))

    ;; Fallback for non-extended reals
    ((and (not (member a *extended-reals*))
          (not (member b *extended-reals*)))
     (ftake 'mexpt a b))

    ;; Special cases
    ((and (eq a '$minf) (integerp b)) ;minf^integer
      (cond ((< b 0) 0)         ;minf^negative integer = 0
            ((eql 0 b) '$und)   ;minf^0 = und
            ((oddp b) '$minf)   ;minf^(odd positive) = minf
            ((evenp b) '$inf)   ;minf^(even positive) = inf
            (t '$und)))         ;shouldn't happen

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
         (t 
              (push (ftake 'mlist a b) *missing*)
         (ftake 'mexpt a b))))))) ; fall back

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

;; I'm not sure what else this might do? I suppose sum(inf,k,a,b) =
;; inf when a < b would be OK. For now, it does nothing.
(def-extended-real-evaluator %sum (e)
  (fapply '%sum e))

;; The calculation 

;;  xxx : product(f(i),i,1,inf);
;;  xxx : subst(f(i) = product(g(k),k,1,inf), xxx);
;;  xxx : subst(g(k) = product(w(m),m,1,inf), xxx);

;; finishes, but is very slow and it calls infsimp many times. The
;; calculation with standard Maxima is also slow.

;; TODO: *extended-real-eval* function for polylogarithms
(defun simpab (e)
  (let ((fn (if (consp e) (gethash (mop e) *extended-real-eval*) nil)))
   (cond ((or ($mapatom e) (not (amongl *extended-reals* e))) e) ;early bailout might boost speed
         ((mplusp e) (addn-extended (cdr e)))
         ((mtimesp e) (muln-extended (cdr e)))
         ((mexptp e) (mexpt-extended (second e) (third e)))
         ;; The operator of e has an infsimp routine, so map simpab over 
         ;; the arguments of e and dispatch fn.
         (fn (funcall fn (mapcar #'simpab (cdr e))))
         (($subvarp (mop e)) ;subscripted function
		      (subfunmake 
		      (subfunname e) 
			        (mapcar #'simpab (subfunsubs e)) 
			        (mapcar #'simpab (subfunargs e))))
         (t 
           (fapply (caar e) (mapcar #'simpab (cdr e)))))))

;; Redefine simpinf and infsimp to just call simpab followed by ridofab. 
(defun simpinf (e)
   (ridofab (simpab e)))

(defun infsimp (e)
   (ridofab (simpab e)))

(defun eq-ab (a b)
  (eql (ridofab a) (ridofab b)))

(defun $test_plus_comm ()
  (let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        ;; test a+b = b+a
        (let ((ans1 (add-extended-real a b))
              (ans2 (add-extended-real b a)))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b) bad)))))
    (fapply 'mlist bad)))

(defun $test_plus_assoc ()
  (let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        (dolist (c L)
        ;; test a+(b+c) = (a+b)+c
        (let ((ans1 (add-extended-real a (add-extended-real b c)))
              (ans2 (add-extended-real (add-extended-real a b) c)))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b c) bad))))))
    (fapply 'mlist bad)))

(defun $test_mult_comm ()
  (let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        ;; test a+b = b+a
        (let ((ans1 (mult-extended-real a b))
              (ans2 (mult-extended-real b a)))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b) bad)))))
    (fapply 'mlist bad)))

(defun $test_mult_assoc ()
  (let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        (dolist (c L)
        ;; test a*(b*c) = (a*b)*c
        (let ((ans1 (mult-extended-real a (mult-extended-real b c)))
              (ans2 (mult-extended-real (mult-extended-real a b) c)))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b c) bad))))))
    (fapply 'mlist bad)))

(defun $test_dist ()
  (let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        (dolist (c L)
        ;; test a*(b+c) = a*b + a*c
        (let ((ans1 (mult-extended-real a (add-extended-real b c)))
              (ans2 (add-extended-real 
                        (mult-extended-real a b)
                        (mult-extended-real a c))))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b c) bad))))))
    (fapply 'mlist bad)))


(defun $test_exp () ;test a^b * a^c = a^(b+c)
(let ((L (list '$minf '$zerob '$zeroa '$ind '$und '$inf '$infinity)) (bad nil))
     (dolist (a L)
      (dolist (b L)
        (dolist (c L)
        ;; test a^(b+c) = a^b * a^c
        (let ((ans1 (mexpt-extended a (add-extended-real b c)))
              (ans2 (mult-extended-real 
                        (mexpt-extended a b)
                        (mexpt-extended a c))))
        (when (not (eq-ab ans1 ans2))
          (push (ftake 'mlist a b c) bad))))))
    (fapply 'mlist bad)))