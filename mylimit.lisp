(in-package :maxima)
(macsyma-module limit)

(mfuncall '$load "my-infsimp")
(defun extended-real-p (e)
  (member e (list '$minf '$zeroa '$zerob '$ind '$inf '$infinity '$und)))

;; This is a list of all methods that $limit uses in an effort
;; to determine a limit. Maxima tries these methods from first
;; to last, stopping when a method is successful. If needed, 
;; a function can locally set the value of *limit-methods* --- this
;; is possibly needed to avoid infinite recursion.
(defmvar *limit-methods* (list 'use-mbag-limit-function
                               'use-inequation-limit-function 
                               'use-one-arg-limit-function
                               'use-rational-function-limit-function
                               'use-direct-substitution
                               'use-taylor-limit
                               'use-gruntz
                               ))

;; What special variables did I miss?
(declare-top (special var val lhp? errorsw *behavior-count-now* taylored
 silent-taylor-flag taylor-catch))

(putprop '$und t 'internal)
(putprop '$ind t 'internal)

;; Define *big* and *tiny* to be "big" and "tiny" numbers, respectively. There
;; is no particular logic behind the choice *big* = 2^107 and *tiny* = 1/2^107.
(defvar *big* (expt 2 107))
(defvar *tiny* (div 1 (expt 2 107)))

;; The function conditional-radcan dispatches $radcan on every subexpression of 
;; the form (positive integer)^X. The function extra-mexpt-simp checks if the
;; input has the form (positive integer)^X and dispatches $radcan when it does.
(defun extra-mexpt-simp (e)
	(if (and (mexptp e) (integerp (cadr e)) (> (cadr e) 0)) 
		($radcan e) e))

(defun conditional-radcan (e)
	(scanmap1 #'extra-mexpt-simp e))
          
(defun convert-to-minf (e)
  (when (not ($mapatom e))
    (setq e ($ratsubst '$minf (mul -1 '$inf) e)))
  (when (not ($mapatom e))  
    (setq e ($ratsubst '$inf (mul -1 '$minf) e)))
  e)  

(defun limit (exp var val *i*)
  ;(mtell "limit: exp = ~M ; var = ~M ;  val = ~M ~%" exp var val)
  (my-limit exp var (ridofab val) (if (eq val '$zeroa) '$plus '$minus)))

(defun limit1 (exp var val)
  ;(mtell "limit1 val = ~M ~%" val) 
  (my-limit exp var (ridofab val) (if (eq val '$zeroa) '$plus '$minus)))

(defun radlim (e n d)
  (declare (ignore e n d))
  (merror "called radlim"))

(defun limit2 (n dn var val)
   (declare (ignore n dn))
  (merror "limit2"))

(defun simplim%unit_step (e var val)
	(let ((lim (limit (cadr e) var val 'think)))
    ;(mtell "lim = ~M ~%" lim)
		(cond ((eq lim '$und) '$und)
			  ((eq lim '$ind) '$ind)
			  ((eq lim '$zerob) 0)
			  ((eq lim '$zeroa) 1)
			  ((not (lenient-realp lim)) (throw 'limit nil)) ;catches infinity too
			  ;; catches minf & inf cases
			  ((eq t (mgrp 0 lim)) 0)
			  ((eq t (mgrp lim 0)) 1)
			  (t '$ind))))
(setf (get '$unit_step 'simplim%function) #'simplim%unit_step)

(defun simplim%mabs (e x pt)
  (setq e ($limit (cadr e) x pt))
  (cond ((or (eq e '$zeroa) (eq e '$zerob)) '$zeroa)
        ((eq e '$infinity) '$inf)
        ((eq e '$ind) '$ind)
        (t (ftake 'mabs e))))
(setf (get 'mabs 'simplim%function) #'simplim%mabs)

(defun simplim%sin (e x pt)
	(setq e ($limit (cadr e) x pt)) ;lost direction?
	(cond ((or (eq e '$inf) (eq e '$minf)) '$ind)
        ((eq e '$und) '$ind) ;welll...
        ((member e (list '$infinity '$zerob '$zeroa '$ind)) e)
        (t (ftake '%sin e))))
(setf (get '%sin 'simplim%function) #'simplim%sin)
(setf (get '$sin 'simplim%function) #'simplim%sin)

(defun simplim%cos (e x pt)
	(setq e ($limit (cadr e) x pt)) ;lost direction?
	(cond ((or (eq e '$inf) (eq e '$minf)) '$ind)
        ((eq e '$und) '$ind) ;welll...
        ((member e (list '$infinity '$ind)) e)
        ((member e (list '$zerob '$zeroa)) 1)
        (t (ftake '%cos e))))
(setf (get '%cos 'simplim%function) #'simplim%cos)
(setf (get '$cos 'simplim%function) #'simplim%cos)

(defun simplim%cosh (e x pt)
  (setq e (limit1 (cadr e) x pt))
  (cond ((eq e '$minf) '$inf) ;cosh(-inf) = inf
        ((eq e '$inf) '$inf) ;cosh(inf) = inf
        ((eq e '$infinity) '$infinity) ;cosh(infinity) = infinity
        ((eq e '$ind) '$ind)
        ((or (eq e '$zerob) (eq e '$zeroa)) '$zeroa)
        ((eq e '$und) '$und)
        (t (ftake '%cosh e))))
(setf (get '%cosh 'simplim%function) #'simplim%cosh)

(defun simplim%sinh (e x pt)
  (setq e (limit1 (cadr e) x pt))
  (cond ((eq e '$minf) '$minf) ;sinh(-inf) = -inf
        ((eq e '$inf) '$inf) ;sinh(inf) = inf
        ((eq e '$infinity) '$infinity) ;sinh(infinity) = infinity
        ((eq e '$ind) '$ind) ;sinh(ind) = ind
        ((eq e '$zerob) '$zerob)
        ((eq e '$zeroa) '$zeroa)
        ((eq e '$und) '$und)
        (t (ftake '%sinh e))))
(setf (get '%sinh 'simplim%function) #'simplim%sinh)

(defvar *mexpt* nil)
(defun simplim%mexpt (e x pt)
  (let ((a) (b) (dir) (emag))
     (when (eq pt '$zeroa)
        (setq dir '$plus)
        (setq pt 0))

       (when (eq pt '$zerob)
        (setq dir '$minus)
        (setq pt 0))

      (setq a (my-limit (second e) x pt dir))
      (setq b (my-limit (third e) x pt dir))

      (setq a (convert-to-minf a))
      (setq b (convert-to-minf b))
      (setq a (conditional-radcan a))
      (setq b (conditional-radcan b))
      (setq a ($trigreduce a))
      (setq b ($trigreduce b))
      (setq a (sratsimp a))
      (setq b (sratsimp b))

      (push (list (list 'mlist) a b) *mexpt*)

      ;(mtell "a = ~M ; b = ~M ~%" a b)
      (setq emag (mfuncall '$cabs a))
      (cond ((and a b (not (extended-real-p a)) 
                      (not (extended-real-p b)) 
                (not (and (zerop2 a) (eq t (mgqp 0 b))))  ; not 0^negative
		            (or (off-negative-real-axisp a) (integerp b)))
		   	         (ftake 'mexpt a b))

              ((eq b '$inf)
                (cond ((mgrp 1 emag) 0); (inside unit circle)^inf = 0
                      ((and (mgrp emag 1) (manifestly-real-p a)) '$inf) ;outside unit circle^inf = inf
                      ((mgrp emag 1) '$infinity) ;outside unit circle^inf = inf
                      (t (limit-nounform e x pt dir))))

              ((and (eq a '$inf) (eq t (mgrp b 0))); inf^pos = inf.
                '$inf)

              ((and (eq a '$inf) (eq t (mgrp 0 b))); inf^neg = 0.
                0)

              ((and (eq a '$minf) (integerp b) (> b 0))
                (if ($evenp b) '$inf '$minf))

             ;;(x>1)^minf = 0
             ((and (eq b '$minf) (eq t (mgrp a 1))) 0)
             
             ;; (0 < x < 1)^minf = inf
             ((and (eq b '$minf) (eq t (mgrp 0 a)) (eq t (mgrp a 1))) '$inf)

            (t
                (limit-nounform e x pt dir)))))      
(setf (get 'mexpt 'simplim%function) 'simplim%mexpt)

;; Except for equality, map limit over a mbag. Users who want limit 
;; to map over equality (mequal) will need to do that manually. 
;; When e is something like X < Y or X # Y, we would like for 
;; Maxima to stop looking for for the limit and return a nounform.
(defun use-mbag-limit-function (e x lp dir)
  (if (and (mbagp e) (not (mequalp e)))
         (ftake '(caar e) (mapcar #'(lambda (q) (my-limit q x lp dir)) (cdr e)))  nil)) 
 
(defun inequation-p (e)
  (and (consp e) (consp (car e)) (or (eq (caar e) 'mequal)
                                     (eq (caar e) 'mlessp))))

(defun use-inequation-limit-function (e x lp dir)
  (if (inequation-p e) (list (list '$limit 'simp) e x lp dir)))
           
;; The member check for $infinity works around a weirdness (?) in simpinf
(defun use-one-arg-limit-function (e x lp dir)
  (declare (ignore x lp dir))
  (if (and (null x) (null x) (null lp)) (my-infsimp e) nil))

(defun indeterminate-product-p (l)
  (and (some #'zerop2 l)
       (some #'(lambda (q) (or (eq q '$minf) (eq q '$inf) (eq q '$infinity))) l)))

(defun indeterminate-sum-p (l)
  (and (member '$inf l) (member '$minf l)))

(defvar *missinglimfun* (make-hash-table))

(defun use-direct-substitution (e x lp dir)
  (let (($numer nil) ($%enumer nil) (ee) (fn) (errorsw nil) (lp-save lp) (e-save e)
     (*limit-methods* (list #'use-direct-substitution)))
    (setq lp (ridofab lp))
    (setq e (ridofab e))
    (setq e (conditional-radcan e))

   	(when (and (eql lp-save 0) (eq dir '$plus))
        (setq lp-save '$zeroa))

    (when (and (eql lp-save 0) (eq dir '$minus))
        (setq lp-save '$zerob))

    ;(mtell "Top: e = ~M x = ~M lp = ~M dir = ~M ~%" e x lp dir)
    (setq fn (and (consp e-save) (consp (car e-save)) (get (caar e-save) 'simplim%function)))
   
   	(cond 
		;; When e is a mapatom, substitute lp for x and return.
		(($mapatom e) (maxima-substitute lp x e))
    ;; If e is free of x, return e.
    (($freeof x e) e)
    ;; If e =F(X), where F has a simplim%function, dispatch the limit function.
    (fn (funcall fn e-save x lp-save))
    ;; Limit of sums (we could put a simplim%function on mplus & mtimes.)
	  ((mplusp e)
       (setq ee (mapcar #'(lambda(q) (my-limit q x lp dir)) (cdr e)))
       (if (and (every #'(lambda (q) (and q 
                                          ;(not (extended-real-p q))      
                                          (not (limitp q)))) ee)
                (not (indeterminate-sum-p ee)))
          (addn-extended ee nil) nil))
    ;; Limit of products
    ((and (mtimesp e))
      ;(mtell "e = ~M ~%" e)
      (setq ee (mapcar #'(lambda(q) (my-limit q x lp dir)) (cdr e)))
      ;(setq ee (mapcar #'conditional-radcan ee))
       (if (and (every #'(lambda (q) (and q 
                                          ;(not (extended-real-p q))
                     (not (limitp q)))) ee)
                (not (indeterminate-product-p ee)))
          (muln-extended  ee nil) nil))
    ;; Give up and return nil      
    (t 
      (setf (gethash (mop e) *missinglimfun*) (+ 1 (gethash (mop e) *missinglimfun* 0)))
      nil))))
		
(defun use-gruntz (e x lp dir)
   (let ((ans (errcatch (gruntz1 e x lp dir))))
         (if (and ans (not (among '$gruntz ans))) (car ans) nil)))

;; This function is for internal use in $limit.
(defun gruntz1 (exp var val &rest rest)
  (cond ((> (length rest) 1)
	 (merror (intl:gettext "gruntz: too many arguments; expected just 3 or 4"))))
  (let (($logexpand t) ; gruntz needs $logexpand T
        (newvar (gensym "w"))
	(dir (car rest)))
  (setq val (convert-to-minf val))
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
      (let ((cx ($supcontext)))
	   	    (unwind-protect
		 	  (progn
			    (mfuncall '$assume (ftake 'mlessp 0 '$zeroa)) ; 0 < $zeroa
				  (mfuncall '$assume (ftake 'mlessp '$zerob 0)) ; $zerob < 0
				  (mfuncall '$assume (ftake 'mlessp *large-positive-number* newvar)) ; *large-positive-number* < newvar
				  (mfuncall '$assume (ftake 'mlessp 0 'lim-epsilon)) ; 0<lim-epsilon
				  (mfuncall '$assume (ftake 'mlessp *large-positive-number* 'prin-inf)) ; *large-positive-number* < prin-inf
				  (mfuncall '$activate cx) ;not sure this is needed	
			    (setq exp ($expand exp 0 0)) ;simplify in new context
          (setq exp (conditional-radcan exp))
				  (limitinf exp newvar)) ;compute & return limit
			($killcontext cx))))) ;kill context & forget all new facts.	  

(defun use-taylor-limit (e x lp dir)
  (let ((silent-taylor-flag t) ;haven't checked what this does
        ;($algebraic t) ;not sure this is good
        ($taylor_simplifier #'conditional-radcan) ;needed!
        ($taylordepth 8) ;not sure; 8 is just magic
        (n 2) (ans nil) (lpp (ridofab lp))
        ;; When taylor(e,x,lp) = e, we run the risk of an infinite loop.
        ;; Of the ways to prevent this (a global such as taylored) or a
        ;; global that counts the recursion depth, let me try removing
        ;; use-taylor-limit from *limit-methods*. When taylor(e,x,lp) # e,
        ;; removing use-taylor-limit potentialy makes the limit code less
        ;; powerful.
        (*limit-methods* (list 'use-mbag-limit-function
                               'use-inequation-limit-function 
                               'use-rational-function-limit-function
                               'use-direct-substitution
                               'use-gruntz)))
    ;; Loop until the result of taylor does not vanish. Once the order reaches
    ;; a magic number (34 or greater), terminate the loop and give up.                           
    (while (and (< n 34) (not ans) (eq t (meqp ans 0)))
            (setq ans (car (errcatch ($ratdisrep ($taylor e x lpp n)))))
            (setq n (+ 1 (* n 2)))) ;increment order by two
    
    ;; When ans # 0, dispatch limit on ans; otherwise return nil
    (if ans (my-limit ans x lp dir) nil)))

(defun setup-limit-assumptions (x lp dir)
  ;; generic assumptions
  (mfuncall '$assume (ftake 'mlessp 0 'lim-epsilon)) ; 0 < lim-epsilon
	(mfuncall '$assume (ftake 'mlessp 0 'epsilon)) ; 0 < epsilon
	(mfuncall '$assume (ftake 'mlessp 'lim-epsilon *tiny*)) ; lim-epsilon < *tiny*
	(mfuncall '$assume (ftake 'mlessp 'epsilon *tiny*)) ; epsilon < *tiny*
	(mfuncall '$assume (ftake 'mlessp *big* 'prin-inf)) ; *big* < prin-inf
  (mfuncall '$assume (ftake 'mlessp 0 '$zeroa)) ; 0 < zeroa
  (mfuncall '$assume (ftake 'mlessp '$zeroa *tiny*)) ; zeroa < *tiny*
  (mfuncall '$assume (ftake 'mlessp '$zerob 0)) ; zerob < 0
  (mfuncall '$assume (ftake 'mlessp (mul -1 *tiny*) '$zerob)) ; -*tiny* < $zerob
  ;; Limit point (lp) and limit direction (dir) dependent assumptions
  (setq lp (ridofab lp))
  (cond ((eq lp '$minf)
          (mfuncall '$assume (ftake 'mlessp x (mul -1 *big*)))) ; x < -*big*
        ((eq lp '$inf)
          (mfuncall '$assume (ftake 'mlessp *big* x))) ; *big* < x
        ((eq dir '$minus) ; lp - *tiny* < x < lp
          (mfuncall '$assume (ftake 'mlessp (sub lp *tiny*) x))
          (mfuncall '$assume (ftake 'mlessp x lp)))
        ((eq dir '$plus) ; lp  < x < lp + *tiny*
          (mfuncall '$assume (ftake 'mlessp lp x))
          (mfuncall '$assume (ftake 'mlessp x (add lp *tiny*))))))

(defun transform-limit (e x g lp dir)
  (cond ((eq lp '$inf) ;just substitute g for x in e
	        (values (maxima-substitute g x e) g '$inf '$minus))

	      ((eq lp '$minf) ;limit(f(x),x,minf) = limit(f(-x),x,inf)
	        (values (maxima-substitute (mul -1 g) x e) g '$inf '$minus))

	      ((eq dir '$minus) ;limit(f(x),x,a,minus) = limit(f(a-x),x,0,plus)
          (values (maxima-substitute (sub lp g) x e) g '$zeroa '$plus))

        ((eq dir '$plus) ;limit(f(x),x,a,plus) = limit(f(a+x),x,0,plus)
          (values (maxima-substitute (add lp g) x e) g '$zeroa '$plus))

        (t (merror (intl:gettext "direction must be 'plus' or 'minus'; found: ~M") dir))))

(defvar *limfun* (make-hash-table))
(defun $report()
	(maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *limfun*)
  (mtell "-----------~%")
  (mtell "Missing simplim%function ~%")
  (maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *missinglimfun*)
  (push '(mlist) *mexpt*)
  (mtell "-----------~%"))

;; Return a limit nounform. 
(defun limit-nounform (e x pt &optional dir)
  (cond ((eq pt '$minf) ;no direction for limit point minf
           (list (list '%limit 'simp) e x pt))
        ((eq pt '$inf) ;no direction for limit point inf
           (list (list '%limit 'simp) e x pt))
        ((or (eq dir '$minus) (eq dir '$plus))
           (list (list '%limit 'simp) e x pt dir))
        (t (list (list '%limit 'simp) e x pt))))

(defun limitp (e)
  (and (consp e) (consp (car e)) (eq '%limit (caar e))))

;; fails when a = limit(f(x),x,a,minus) &  b = limit(f(x),x,a,plus).
(defun two-sided-limit-return (a b)
  ;; Convert zeroa & zerob to zero.
  (setq a (ridofab a)
        b (ridofab b))
  (cond ((alike1 a b) a) ;syntaxic equality, return a
        ((or (eq '$und a) (eq '$und b)) '$und) ;one limit is und, return $und
        ;; a=infinity, b= minf or inf, return infinity
        ((and (eq a '$infinity) (or (eq b '$inf) (eq b '$minf))) 
          '$infinity)
        ;; b=infinity, a= minf or inf, return infinity  
        ((and (eq b'$infinity) (or (eq a '$inf) (eq a '$minf))) 
          '$infinity)
        ;; a=ind and b is real valued, return $ind
        ((and (eq a '$ind) (manifestly-real-p b)) '$ind)
        ;; b=ind and a is real valued, return $ind
        ((and (eq b '$ind) (manifestly-real-p a)) '$ind)
        ;; ask if a = b; if yes, return a; if not, return $und

        ((and (limitp a) (limitp b) 
              (alike1 (second a) (second b))
              (alike1 (third a) (third b))
              (alike1 (third a) (third b)))
            (limit-nounform (second a) (third a) (fourth a)))

        ((and ($freeof '%limit a) ($freeof '%limit b))
           (if (eq '$yes ($askequal a b)) a '$und))
        ;; Give up and return $und
        (t '$und)))
       
(defun my-limit (e x lp dir)
   (let ((ee e) (lp-save lp) (dir-save dir) (ans) (gvar (gensym "g")) (cntx) (*behavior-count-now* 0) (errorsw nil) (lhp? nil))
      (unwind-protect 
        ;; In a super context, make assumptions appropriate for the limit point
        ;; and limit direction. The simplify e in the new context.
        (progn
          (setq cntx ($supcontext))
          ($activate cntx)
          (let ((*atp* t)) 
            (multiple-value-setq (e gvar lp dir) (transform-limit e x gvar lp dir)))
          (setup-limit-assumptions gvar lp dir) ;make assumptions
          (setq e ($expand e 0 0)) ;simplify in new context
          (setq e (conditional-radcan e))
          ;; Loop through the methods and stop when we have a value. Special case
          ;; the one variable case.
          (catch 'limit
            (dolist (lm *limit-methods*)
	           	(setq ans (funcall lm e gvar lp dir))
              (setq ans (convert-to-minf ans))
		          (when (and ans (not (among '%limit ans))) ;($freeof '%limit ans))
                (setf (gethash lm *limfun*) (+ 1 (gethash lm *limfun* 0)))
                (throw 'limit ans))))

          ;; Maybe the final call to sratsimp is spendy. But...
          (cond ((and ans (not (among '%limit ans))) (sratsimp ans))
                (t (limit-nounform ee x lp-save dir-save))))
          ($killcontext cntx))))

;; This is the top level call for limit. Mostly it checks that the 
;; arguments are OK and calls my-limit. For a two sided limit, it
;; calls my-limit twice & compares the results.

;; Bug: transform-limit makes a mess of things like limit(x<6,x,8).
;; Not sure what to do--could attempt to trap all such expressions
;; in transform-limit?     

;; Locally setting domain to complex and m1pbranch to t might be
;; controversial. But without these assignments to option variables
;; limit((x^(1/x) - 1)*sqrt(x), x, 0, minus) = nounform.But 
;; integrate(x*exp(-x^2)*sin(x),x,minf,inf) errors when domain is complex.
(defmfun $limit (e &rest xxx)
   (let ((x nil) (lp nil) (dir) 
         ;($domain '$complex)  ;I'm not a control freak--setting all these options
         ;($m1pbranch t)       ;helps locate bugs. 
         ;($algebraic t)       
         ;($ratsimpexpons nil) ;Setting ratsimpexpons to true causes nasty bugs.
         ;($%emode t)
         ;($%enumer nil)
         ;($numer nil)
         ;($demoivre nil)
         ;($lognegint t)
         ;($logexpand nil)
         ;($logsimp t)
         ;($ratfac nil)
         ;($logarc nil) ;$logarc t causes some problems?
         ;($factor_max_degree_print_warning nil)
         ;($%e_to_numlog t)
         )
      (when xxx 
        (setq x (pop xxx)))
  
      (when (not ($mapatom x))
        (merror (intl:gettext "Limit variable must be a mapatom; found ~M") x))

      (when (kindp x '$constant)
         (merror (intl:gettext "Limit variable must not be constant; found ~M") x))
       
      ;; Error when exactly two arguments  
      (when (and x (not xxx))
        (wna-err '$limit))

      (setq lp (pop xxx))
      (when (eq lp '$infinity) ;what else? lp is a list, zeroa, ind, what?
         (merror (intl:gettext "Limit point cannot be infinity")))

      ;(setq lp (convert-to-minf lp))
      (setq dir 
         (cond (xxx (pop xxx))
               ((eq lp '$inf) '$minus) 
               ((eq lp '$minf) '$plus) 
               (t '$both))) ;assume two-sided limit when direction isn't given.

      ;; The limit point must be either 'minus', 'plus', or 'both':
      (when (not (member dir (list '$minus '$plus '$both)))
        (merror (intl:gettext "Limit direction must be 'minus', 'plus' or 'both'; found: ~M") dir))

      ;; Error when more then four arguments
      (when xxx
        (wna-err '$limit))

      (cond ((eq dir '$both)
              (two-sided-limit-return 
                     (my-limit e x lp '$minus)
                     (my-limit e x lp '$plus)))
            (t  (my-limit e x lp dir)))))    
     
(defun polynomial-leading-term (e x)
   (let ((n) (cf) (ans))
     (setq e ($expand e))  
     (cond ((eq t (meqp e 0)) 0)
           ((not (mplusp e)) e)
           (t 
             ;; When n is a max expression, for example n = max(a,b,1/2), we
             ;; could, I suppose, ask the user to choose the largest memember.
             (setq n ($hipow e x)) 
             (cond ((subexp e (ftake 'mexpt x n))
                    (setq cf ($coeff e x n))
                    (setq ans (mul cf (ftake 'mexpt x n)))
                    (if (eq '$yes ($askequal cf 0))
                        (polynomial-leading-term ($ratsubst 0 ans e) x)
                        ans))
                    (t nil))))))

(defun use-rational-function-limit-function (e x lp dir)  
   (let ((a) (b) (n) (cf) (ans) (sgn-n))
      (cond ((and (eq lp '$inf) (eq dir '$minus))
              (setq e (sratsimp e))
              (setq a ($expand ($num e)))
              (setq b ($expand ($denom e)))
              (labels ((cf (s) ($freeof x s))
                       (exponf (s) ($freeof x s)))
              (cond ((and ($polynomialp a (ftake 'mlist x) #'cf #'exponf)
                          ($polynomialp b (ftake 'mlist x) #'cf #'exponf))
                    (setq a (polynomial-leading-term a x))
                    (setq b (polynomial-leading-term b x))
                    (cond ((and a b)
                            (setq ans (sratsimp (div a b)))
                            (setq n ($hipow ans x))
                            (setq cf ($coeff ans x n))
                            (cond ((eq '$yes ($askequal 0 ($imagpart n)))
                                   (setq sgn-n ($asksign n))
                                   (cond ((eq sgn-n '$neg) 0) ;limit(cf*x^neg,x,inf) = 0
                                         ((eq sgn-n '$zero) cf) ;limit(cf,x,inf) = cf
                                         ((eq sgn-n '$pos) (mul cf '$inf))))
                                    (t '$und)))
                            (t nil))))))               
                  (t nil))))
             
    
  