
; Define *big* and *tiny* to be "big" and "tiny" numbers, respectively. There
;; is no particular logic behind the choice *big* = 2^107 and *tiny* = 1/2^107.
(defvar *big* (expt 2 107))
(defvar *tiny* (div 1 (expt 2 107)))

;; Insert a call to asymptotic-expansion into gruntz1. Additionally
;; insert some assume stuff, but I'm not sure that any of this is
;; needed. Otherwise, this code is the same as the gruntz1 code in 
;; limit.lisp.

(defun gruntz1-xxxx (exp var val &rest rest)
   (cond ((> (length rest) 1)
	 (merror (intl:gettext "gruntz: too many arguments; expected just 3 or 4"))))
  (let (($logexpand t) ; gruntz needs $logexpand T
        (newvar (gensym "w"))
	(dir (car rest)))
	(putprop newvar t 'internal); keep var from appearing in questions to user	
    (cond ((eq val '$inf)
	   (setq exp (maxima-substitute newvar var exp)))
	  ((eq val '$minf)
	   (setq exp (maxima-substitute (m* -1 newvar) var exp)))
	  ((eq val '$zeroa)
	   (setq exp (maxima-substitute (m// 1 newvar) var exp)))
	  ((eq val '$zerob)
	   (setq exp (maxima-substitute (m// -1 newvar) var exp)))
	  ((eq dir '$plus)
	   (setq exp (maxima-substitute (m+ val (m// 1 newvar)) var exp)))
	  ((eq dir '$minus)
	   (setq exp (maxima-substitute (m+ val (m// -1 newvar)) var exp)))
	  (t (merror (intl:gettext "gruntz: direction must be 'plus' or 'minus'; found: ~M") dir)))
  
       (let ((cntx ($supcontext)) (val '$inf)) ;not sure about locally setting val?
	   	    (unwind-protect
		 	  (progn
	    	      (mfuncall '$assume (ftake 'mlessp 0 'lim-epsilon)) ; 0 < lim-epsilon
	    	      (mfuncall '$assume (ftake 'mlessp 0 'epsilon)) ; 0 < epsilon
				  (mfuncall '$assume (ftake 'mlessp 'lim-epsilon *tiny*)) ; lim-epsilon < *tiny*
			      (mfuncall '$assume (ftake 'mlessp 'epsilon *tiny*)) ; epsilon < *tiny*
				  (mfuncall '$assume (ftake 'mlessp *big* 'prin-inf)) ; *big* < prin-inf
			      (mfuncall '$assume (ftake 'mlessp 0 '$zeroa)) ; 0 < $zeroa
				  (mfuncall '$assume (ftake 'mlessp '$zeroa *tiny*)) ; $zeroa < *tiny*
				  (mfuncall '$assume (ftake 'mlessp '$zerob 0)) ; $zerob < 0
				  (mfuncall '$assume (ftake 'mlessp (mul -1 *tiny*) '$zerob)) ; -*tiny* < $zerob
				  (mfuncall '$assume (ftake 'mlessp *big* newvar)) ; *big* < newvar
				  (mfuncall '$activate cntx) ;not sure this is needed, but OK			
				  (setq exp (sratsimp exp)) ;simplify in new context
                  (setq exp (asymptotic-expansion exp newvar '$inf 1));pre-condition
				  (limitinf exp newvar)) ;compute & return limit
		    ($killcontext cntx))))) ;forget facts
            
;; The function conditional-radcan dispatches $radcan on every subexpression of 
;; the form (positive integer)^X. The function extra-mexpt-simp checks if the
;; input has the form (positive integer)^X and dispatches $radcan when it does.
(defun extra-mexpt-simp (e)
	(if (and (mexptp e) (integerp (cadr e)) (> (cadr e) 0)) 
		($radcan e) e))

(defun conditional-radcan (e)
	(scanmap1 #'extra-mexpt-simp e))

(defun function-transform (e x)
  (let ((fn) (gn))
	(cond (($subvarp e) e) ;return e
	      ((extended-real-p e) e) ;we don't want to call sign on ind, so catch this
		  (($mapatom e) ;if e declared zero, return 0; otherwise e
		    (if (eq '$zero ($csign e)) 0 e))
	      ((mplusp e); when X depends on x,  do cos(X)^2 + sin(X)^2 --> 1
		    (pythagorean-cos-sin-simp e x))
		  (t
		    (setq fn (mop e))
			(setq gn (if (symbolp fn) (get fn 'recip) nil))
           
            (cond 
			 ;; exponentialize hyperbolic trig functions when they depend on x
			((and (member fn (list '%cosh '%sech '%sinh '%csch '%tanh '%coth))
				  (not (freeof x e)))
				($exponentialize e))
		   
		   	 ;; do X^Y --> exp(Y log(X)) when both X & Y depend on x
			((and (eq fn 'mexptp) 
		          (not (freeof x (cadr e)))
	              (not (freeof x (caddr e))))
	          (ftake 'mexpt '$%e (mul (caddr e) (ftake '%log (cadr e)))))
			
			 ;; conditional radcan
			((eq fn 'mexpt) (extra-mexpt-simp e))
			;; Do cot --> 1/tan, sec --> 1/cos, ...
			((and gn (member fn (list '%cot '%sec '%csc '%jacobi_ns '%jacobi_ds '%jacobi_dc))
					(not (freeof x e)))
				   (div 1 (simplifya (cons (list gn) (margs e)) t)))
            ;; acsc(x) --> asin(1/x)
            ((and (eq fn '%acsc) (not (freeof x (cadr e))))
				    (ftake '%asin (div 1 (cadr e))))
			;; asec(x)--> acos(1/x)
			((and (eq fn '%asec) (not (freeof x (cadr e))))
				    (ftake '%acos (div 1 (cadr e))))
            ;; acot(x) --> atan(1/x)
			((and (eq fn '%acot) (not (freeof x (cadr e))))
				    (ftake '%atan (div 1 (cadr e))))
            ;; acsch(x) --> asinh(1/x)
			((and (eq fn '%acsch) (not (freeof x (cadr e))))
				    (ftake '%asinh (div 1 (cadr e))))
            ;; asech(x) --> acosh(1/x)
			((and (eq fn '%asech) (not (freeof x (cadr e))))
				    (ftake '%acosh (div 1 (cadr e))))
            ;; acoth(x) --> atanh(1/x)
			((and (eq fn '%acoth) (not (freeof x (cadr e))))
				    (ftake '%atanh (div 1 (cadr e))))
            ;; gamma to factorial
			((and (eq fn '%gamma) (not (freeof x (cadr e))))
				($makefact e))
			;; convert binomial coefficient to gamma form
			((and (eq fn '%binomial) (not (freeof x (cdr e))))
				($makegamma e))
            ;; convert Fibonacci to power form
            ((and (eq fn '$fib) (not (freeof x (cadr e))))
			   ($fibtophi e))
            ;; No more simplifications--give up
			(t e))))))

;; First, dispatch trigreduce. Second convert all trigonometric functions to 
;; cos, sin, cosh, and sinh functions.
(defun trig-to-cos-sin (e)
  (let (($opsubst t))
    ;(setq e ($trigreduce e))
    (setq e ($substitute #'(lambda (q) (div (ftake '%sin q) (ftake '%cos q))) '%tan e))
    (setq e ($substitute #'(lambda (q) (div (ftake '%cos q) (ftake '%sin q))) '%cot e))
    (setq e ($substitute #'(lambda (q) (div 1 (ftake '%cos q))) '%sec e))
    (setq e ($substitute #'(lambda (q) (div 1 (ftake '%sin q))) '%csc e))
    (setq e ($substitute #'(lambda (q) (div (ftake '%sinh q) (ftake '%cosh q))) '%tanh e))
    (setq e ($substitute #'(lambda (q) (div (ftake '%cosh q) (ftake '%sinh q))) '%coth e))
    (setq e ($substitute #'(lambda (q) (div 1 (ftake '%cosh q))) '%sech e))
    (setq e ($substitute #'(lambda (q) (div 1 (ftake '%sinh q))) '%csch e))
    (sratsimp e)))
		
(defun limit-simplify(e x pt)
	;(let (($algebraic t))
	  ;; causes trouble (setq e (trig-to-cos-sin e))
  	  (setq e ($expand e 0 0)) ;simplify in new context
	  (setq e ($minfactorial e))
	  (mfuncall '$scanmap #'(lambda (q) (function-transform q x)) e '$bottomup));)
   
;; True iff the operator of e is %cos.
(defun cosine-p (e)
  (and (consp e) (consp (car e)) (eq '%cos (caar e))))

;; Gather the non-atomic subexpressions of e that satisfy the predicate fn
(defun my-gather-args (e fn)
   (cond (($mapatom e) nil)
		  ((funcall fn e) (cdr e))
		  (t 
		    (reduce #'append (mapcar #'(lambda (q) (my-gather-args q fn)) (cdr e))))))
		
;; Replace cos(X)^2 + sin(X)^2 by 1 when X depends on x.
 (defun pythagorean-cos-sin-simp (e x)
	(let ((ccc nil) (z) (ee))
	  (cond (($mapatom e) e)
	        ((mplusp e)
	            (setq ccc (my-gather-args e 
				    #'(lambda (q) (and (cosine-p q) (not (freeof x q))))))
	   	        (dolist (g ccc)
			        (setq z (gensym))
			        (setq ee (maxima-substitute z (power (ftake '%cos g) 2) e))
			        (setq ee (maxima-substitute (sub 1 z) (power (ftake '%sin g) 2) ee))
			        (setq ee (sratsimp ee))
			        (when (freeof z ee)
			            (setq e ee)))
				e)
			;; maybe this isn't needed, but I think it's not wrong.
			((eq 'mqapply (caar e))
			  (subftake (caar (second e))
			     (mapcar #'(lambda (q) (pythagorean-cos-sin-simp q x)) (subfunsubs e))
			     (mapcar #'(lambda (q) (pythagorean-cos-sin-simp q x)) (subfunargs e)))) 
			;; map pythagorean-cos-sin-simp over the args
			(t 
			 (simplifya (cons (list (caar e)) 
			  (mapcar #'(lambda (q) (pythagorean-cos-sin-simp q x)) (cdr e))) t)))))
;;;;

;; Return true iff e is an symbol & and extended real. The seven extended reals 
;; are minf, zerob, zeroa, ind, inf, infinity, and und. Maybe this could be extended 
;; to include epsilon and prin-inf.
(defun extended-real-p (e)
  (member e (list '$minf '$zerob '$zeroa '$ind '$inf '$infinity '$und)))

;; We use a hashtable to represent the addition table of the extended real numbers.
;; Arguably the hashtable isn't the most compact way to to this, but this scheme 
;; makes it easy to extend and modify. 

;; Since limit ((x,y)-> (0+, 0-) (x+y) = 0, we use 0+ + 0- = 0.
;; Similarly for all other cases involving the limit points 
;; zerob & zeroa, we conclude that for addition zeroa and zerob
;; should be treated the same as zero. Thus this addition table
;; doesn't include zeroa and zerob.
(defvar *extended-real-add-table* (make-hash-table :test #'equal))

(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-add-table*) (third a)))
   (list (list '$minf '$minf '$minf)
         (list '$minf '$inf '$und)
         (list '$minf '$infinity '$und)
         (list '$minf '$und '$und)
         (list '$minf '$ind '$minf)
         
         (list '$inf '$inf '$inf)
         (list '$inf '$infinity '$und)
         (list '$inf '$und '$und)
         (list '$inf '$ind '$inf)

         (list '$infinity '$infinity '$und)
         (list '$infinity '$zerob '$infinity)
         (list '$infinity '$zeroa '$infinity)
         (list '$infinity '$und '$und)
         (list '$infinity '$ind '$infinity)

         (list '$ind '$ind '$ind)
         (list '$ind '$und '$und)

         (list '$und '$und '$und)))

;; Add extended reals a & b. When (a,b) isn't a key in the hashtable, return
;; $und. The table is symmetric, so we look for both (a,b) and if that fails,
;; we look for (b,a).
(defun add-extended-real(a b)
  (gethash (list a b) *extended-real-add-table* 
    (gethash (list b a) *extended-real-add-table* '$und)))

;; Add an expression x to a list of infinities l. This code effectively 
;; converts zeroa & zerob to 0. Maybe that should be revisited. Arguably
;; x + minf --> minf is wrong because if x = inf it's wrong. Again, that
;; could be revisited.
(defun add-expr-infinities (x l) 
  ;; Add the members of this list of extended reals l.
  (setq l (cond ((null l) 0)
                ((null (cdr l)) (car l))
                (t (reduce #'add-extended-real l))))

  (cond ((eql l 0) x)          ;x + 0 = x
        ((eq l '$inf) '$inf)   ;x + inf = inf
        ((eq l '$minf) '$minf) ;x + minf = minf
        ((eq l '$infinity) '$infinity) ;x + infinity = infinity
        ((eq l '$ind) '$ind) ; x + ind = ind
        ((eq l '$und) '$und) ;x + und = und
        ;; Give up and return a nounform. But this shouldn't happen!
        (t (list (get 'mplus 'msimpind) (sort (list x l) '$orderlessp)))))

;; Add a list of expressions, including extended reals. When the optional
;; argument flag is true, dispatch infsimp on each list member before adding.
(defun addn-extended (l &optional (flag t))
  (setq l (mapcar #'ridofab l)) ;convert zerob/a to zero.

  (when flag
    (setq l (mapcar #'my-infsimp l)))

  (let ((xterms nil) (rterms 0))
    (dolist (lk l)
      (if (extended-real-p lk) (push lk xterms) (setq rterms (add lk rterms))))
    (add-expr-infinities rterms xterms)))      

;;We use a hashtable to represent the multiplication table for extended 
;; real numbers. The table is symmetric, so we only list its "upper" half.
(defvar *extended-real-mult-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-mult-table*) (third a)))
   (list (list '$minf '$minf '$inf)
         (list '$minf '$inf '$minf)
         (list '$minf '$infinity '$infinity)
         (list '$minf '$und '$und)
         (list '$minf '$ind '$und)
         
         (list '$inf '$inf '$inf)
         (list '$inf '$infinity '$infinity)
         (list '$inf '$und '$und)
         (list '$inf '$ind '$und)

         (list '$infinity '$infinity '$infinity)
         (list '$infinity '$und '$und)
         (list '$infinity '$ind '$und)

         (list '$ind '$ind '$ind)
         (list '$ind '$und '$und)

         (list '$und '$und '$und)))

;; Multiply extended reals a & b. When (a,b) isn't a key in the hashtable, return
;; $und. The table is symmetric, so we look for both (a,b) and if that fails,
;; we look for (b,a). Maybe zeroa/b*ind could be 0? This code misses this case
(defun mult-extended-real (a b)
  (gethash (list a b) *extended-real-mult-table* 
	    (gethash (list b a) *extended-real-mult-table* '$und)))

(defun muln-extended (l &optional (flag t))
  (when flag
    (setq l (mapcar #'my-infsimp l)))

  (let ((xterms nil) (rterms 1))
    (dolist (lk l)
      (if (extended-real-p lk) (push lk xterms) (setq rterms (mul lk rterms))))
    (mult-expr-infinities rterms xterms)))      

(defmfun $askcsign (e)
  (let ((ans (errcatch ($csign e))))
    (if ans (car ans) '$complex)))
    
;; Return a*b without dispatching the simplifier on the product. But we do
;; properly sort the argument list. Ahh should the sort predicate be great
;; or '$orderlessp?
(defun nounform-mult (a b)
  (list (get 'mtimes 'msimpind) (sort (list a b) '$orderlessp)))

(defun mult-expr-infinities (x l) 
  (let ((sgn))
    (setq sgn ($askcsign x))  ;set ans to the complex sign of x

    (setq l (cond ((null l) 1)
                  ((null (cdr l)) (car l))
                  (t (reduce #'mult-extended-real l))))
    (setq l (ridofab l)); not sure   
    (cond ((eq l '$minf)
             (cond ((eq sgn '$neg) '$inf)
                   ((eq sgn '$pos) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((or (eq sgn '$complex) (eq sgn '$imaginary)) '$infinity)
                   (t (nounform-mult x l))))

          ((eql l 1) x) ;X*1 = X
          ((eql l 0) 0) ;X*0 = 0

          ((eq l '$inf)
             (cond ((eq sgn '$neg) '$minf)
                   ((eq sgn '$zero) '$und)
                   ((eq sgn '$pos) '$inf)
                   ((or (eq sgn '$complex) (eq sgn '$imaginary)) '$infinity)
                   (t (nounform-mult x l))))
          ((eq l '$ind) 
            (if (eq sgn '$zero) 0 '$ind))
          ((eq l '$infinity) ;0*infinity = und & X*infinity = infinity.
            (if (eq sgn '$zero) '$und '$infinity))
          ((eq l '$und) '$und)
          (t (nounform-mult x l)))))

(defun muln-extended (l &optional (flag t))
    (when flag
      (setq l (mapcar #'my-infsimp l)))
    (let ((xterms nil) (rterms 1))
    (dolist (lk l)
      (if (extended-real-p lk) (push lk xterms) (setq rterms (mul lk rterms))))
    (mult-expr-infinities rterms xterms)))        

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
  (let ((amag ($cabs a)))

  (cond ((gethash (list a b) *extended-real-mexpt-table* nil)) ;look up

        ((eq b '$inf)
          (cond ((eq t (mgrp 1 amag)) 0); (inside unit circle)^inf = 0
                ((and (eq t (mgrp amag 1)) (manifestly-real-p a)) '$inf) ;outside unit circle^inf = inf
                ((eq t (mgrp amag 1)) '$infinity) ;outside unit circle^inf = inf
                (t (ftake 'mexpt a b))))

        ;; inf^pos = inf.
        ((and (eq a '$inf) (eq t (mgrp b 0))) '$inf)
        ;; inf^neg = 0. 
        ((and (eq a '$inf) (eq t (mgrp 0 b)))  0)
        ;; minf^integer
        ((and (eq a '$minf) (integerp b) (> b 0))
          (if ($evenp b) '$inf '$minf))
        ((and (eq a '$minf) (integerp b) (< b 0)) 0)  
        ;;(x>1)^minf = 0
        ((and (eq b '$minf) (eq t (mgrp a 1))) 0)
        ;; (0 < x < 1)^minf = inf
        ((and (eq b '$minf) (eq t (mgrp 0 a)) (eq t (mgrp a 1))) '$inf)
        (t (ftake 'mexpt a b)))))

;; functions only intended for testing
(defun $infsimp (e)
  (my-infsimp e))

(defun $mul (&rest a)
   (muln-extended a t))

(defun $add (&rest a)
   (addn-extended a t))

(defvar *extended-real-eval* (make-hash-table :test #'equal))

(defun log-of-extended-real (e)
  (setq e (my-infsimp (car e)))
  (mtell "e = ~M ~%" e)
  (cond ((eq e '$minf) '$infinity)
        ((eq e '$zerob) '$infinity)
        ((eq e '$zeroa) '$minf)
        ((eq e '$ind) '$und)
        ((eq e '$und) '$und)
        ((eq e '$inf) '$inf)
        ((eq e '$infinity) '$infinity)
        (t (ftake '%log e))))
(setf (gethash '%log *extended-real-eval*) #'log-of-extended-real)

(defun my-infsimp (e)
  (let ((fn (if (and (consp e) (consp (car e))) (gethash (caar e) *extended-real-eval*) nil)))
  (cond (($mapatom e) e)
        ((mbagp e) ;map my-infsimp over lists & such
          (simplifya (cons (list (caar e)) (mapcar #'my-infsimp (cdr e))) t))
        ((mplusp e)
          (addn-extended (cdr e) t))
        ((mtimesp e)
          (muln-extended (cdr e) t))
        ((mexptp e)
          (mexpt-extended (my-infsimp (second e)) (my-infsimp (third e))))
        (fn (funcall fn (cdr e)))
        ;; not sure about this--subscripted functions?
      (t (simplifya (cons (list (caar e)) (mapcar #'infsimp (cdr e))) t)))))

