;;; Maxima code for finding asymptotic expansions of various functions, including 
;;; bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, 
;;; polylogarithm, and polygamma functions. 

;;; The purpose of this code is for computing limits. Specifically
;;; limit(e,x,pt) = limit(asymptotic-expansion(e,x,pt),x,pt) is supposed to be
;;; an identity. Possibly asymptotic-expansion could be promoted to a user level 
;;; function, but for now it isn't intended to be a user level function.

;;; Copyright (C) 2022 Barton Willis
;;; Department of Mathematics 
;;; University of Nebraska at Kearney
;;; Kearney NE 68847
;;; willisb@unk.edu

;;; This source code is licensed under the terms of the Lisp Lesser 
;;; GNU Public License (LLGPL). The LLGPL consists of a preamble, published
;;; by Franz Inc. (http://opensource.franz.com/preamble.html), and the GNU 
;;; Library General Public License (LGPL), version 2, or (at your option)
;;; any later version.  When the preamble conflicts with the LGPL, 
;;; the preamble takes precedence. 

;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Library General Public License for details.

;;; You should have received a copy of the GNU Library General Public
;;; License along with this library; if not, write to the
;;; Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
;;; Boston, MA  02110-1301, USA.

(in-package :maxima)

;; What special variables did I miss?
(declare-top (special var val lhp? taylored silent-taylor-flag
   $taylordepth $taylor_logexpand $maxtaylororder $taylor_simplifer))

;; Define *big* and *tiny* to be "big" and "tiny" numbers, respectively. There
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

;; Redefine the function stirling0. The function stirling0 does more than its
;; name implies, so we will effectively rename it to asymptotic-expansion.

;; The identifiers var and val look too similar to me--I'm going to use x for
;; the limit variable and pt for the limit point.
(defun stirling0 (e &optional (x var) (pt val) (n 1))
	(asymptotic-expansion e x pt n))

;; Hash table: key is a function name (for example, %gamma) with the 
;; corresponding value a CL function that produces an asymptotic 
;; expansion for the function with that key. Each function has
;; the signature fn(e,x,pt,n), where e is a CL list of the arguments
;; of the function being expanded, x is the limit variable, pt is 
;; the limit point, and n is the truncation order. When these functions
;; cannot find the expansion, the returned value is a nounform
;; for the function.
(defvar *asymptotic-expansion-hash* (make-hash-table :test #'eq :size 16))

;; Maybe not intended to be a user level function?
(defun $asymptotic_expansion (e x pt n)
	(asymptotic-expansion e x pt n))

;; For experimentation, let's collect all operators don't have a specialized 
;; asymptotic expansion function in a hashtable *xxx*. The function $missing
;; prints a report on these missing operators. Similarly collect the operators
;; that are used. Eventually remove this code.
(defvar *xxx* (make-hash-table))
(defvar *used* (make-hash-table))

(defun $missing()
    (mtell "Missing operators: ~%")
	(maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *xxx*)
    (mtell "Used operators: ~%")
	(maphash #'(lambda (a b) (mtell "~M ~M ~%" a b)) *used*))

;; For the expression e, replace various functions (gamma, polylogarithm, and ...)
;; functions with a truncated asymptotic (Poincaré) expansions. We walk through
;; the expression tree and use hashtable to find operators with a
;; specialized function for an asymptotic expansion. When we find such an
;; operator, dispatch the function from the hashtable.

;; fff is only used to enumerate the used operators--eventually delete this stuff
(defun asymptotic-expansion (e x pt n)
	(let (($gamma_expand nil) ;not sure about these option variables
	      ($numer nil)
		  ($float nil)
		  ;($domain '$complex) ;extra not sure about this
		  ;($m1pbranch t)
		  ($algebraic t)
	      (fn nil) (args nil) (lhp? nil) (fff))
	      
        ;; Unify dispatching an *asymptotic-expansion-hash* function for both 
		;; subscripted and non subscripted functions. For a subscripted
		;; function, args = (append subscripted args, regular args).
        (cond ((and (consp e) (consp (car e)) (eq 'mqapply (caar e)))
		           (setq fff (subfunname e))
                   (setq fn (gethash (subfunname e) *asymptotic-expansion-hash* nil))
                   (setq args (append (subfunsubs e) (subfunargs e))))
	            ((and (consp e) (consp (car e)))
				    (setq fff (caar e))
			        (setq fn (gethash (caar e) *asymptotic-expansion-hash* nil))
                    (setq args (cdr e))))

		(when fn
		   (setf (gethash fff *used*) (+ 1 (gethash fff *used* 0))))

		(cond (($mapatom e) e)
			  (fn (apply fn (list args x pt n)))
	   	      (t 
			    ;; For an arbitrary operator, likely it's OK to map 
				;; asymptotic-expansion over the arguments. But I'm not
				;; sure we win by doing so. Plus some of the limit code is
				;; overly sensitive to syntactic changes to internal expressions--
				;; so let's not make syntactic changes that don't matter.
				(setf (gethash (caar e) *xxx*) (+ 1 (gethash (caar e) *xxx* 0)))
			    e))))
			
;; For a sum, map asymptotic-expansion onto the summand and sum the result. When
;; the sum vanishes, increase the truncation order and try again. When the order n 
;; reaches a magic number (8), give up and return e. 

;; The first argument e is a CL list of the summand. The second argument is the 
;; limit variable, the third is the point, and the last is the truncation level.

(defvar *zero-case* 0) ;for experimentation only
(defun mplus-asymptotic (e x pt n)
    (let ((ans))
	    (setq ans (addn (mapcar #'(lambda (s) (asymptotic-expansion s x pt n)) e) t))
        ;(setq ans (sratsimp ans)) ;needed or unneeded?
        (while (and (zerop1 (sratsimp ans)) (< n 8)) ;magic number 8.
			(mtell "Caught a zero case! ~%") ;untested!
			(setq *zero-case* (+ 1 *zero-case*))
			(setq n (+ 1 n))
			(setq ans (mplus-asymptotic e x pt n)))
         (if (zerop1 ans) (addn e t) ans))) ;when ans is still zero, sum e and return
(setf (gethash 'mplus *asymptotic-expansion-hash*) #'mplus-asymptotic)

;; Return the product of the result of mapping asymptotic-expansion over the terms 
;; in the CL list e.
(defun mtimes-asymptotic (e x pt n)
	(muln (mapcar #'(lambda (s) (asymptotic-expansion s x pt n)) e) t))
(setf (gethash 'mtimes *asymptotic-expansion-hash*) #'mtimes-asymptotic)

;; The general simplifier doesn't simplify, for example, 4^x/(2^(2x)) to 1.
;; This causes some bugs in evaluating limits. Here we sneak in a radcan on
;; on (positive integer)^anything. I think this hack(?) eliminates several
;; testsuite failures.
(defun mexpt-asymptotic (e x pt n)
	(let ((a (car e)) (b (cadr e)) (ans))
		(setq a (asymptotic-expansion a x pt n))
		(setq b (asymptotic-expansion b x pt n))
		(setq ans (conditional-radcan (ftake 'mexpt a b)))
		ans))
		;(or ($ratdisrep (tlimit-taylor ans x pt n)) ans)))
   	(setf (gethash 'mexpt *asymptotic-expansion-hash*) #'mexpt-asymptotic)

;; Could we do better? Maybe  
;;   log(x^2+x) -> log(x^2) + 1/x-1/(2*x^2)+1/(3*x^3)
(defvar *log-arg* nil)
(defun log-asymptotic (e x pt n)
	(ftake '%log (asymptotic-expansion (first e) x pt n)))
;	(setq e (cadr e))
 ;   (let ((xxx ($limit e x pt)))
;	   (if (eq xxx '$inf) ($ratdisrep ($taylor (ftake '%log e) x '$inf n))
;	      (ftake '%log e))))
(setf (gethash '%log *asymptotic-expansion-hash*) #'log-asymptotic)

;; There are other cases: xxx is positive, for example.
(defun mabs-asymptotic (e x pt n)
   (setq e (car e))
   (let ((xxx ($limit e x pt)))
      (cond ((eq xxx '$ind)
	         (ftake 'mabs e))	  
	        ((eq t (mgrp xxx 0)) ;new!
	         (asymptotic-expansion e x pt n))
			((eq t (mgrp 0 xxx)) ;new!
	         (asymptotic-expansion (mul -1 e) x pt n)) 
	        (t (ftake 'mabs e)))))
(setf (gethash 'mabs *asymptotic-expansion-hash*) #'mabs-asymptotic)

;; See https://dlmf.nist.gov/6.12.  Let's triple check for a Ei vs E1 flub.
(defun expintegral-ei-asymptotic (e x pt n)
	(setq e (first e))
	(cond ((eq '$inf ($limit e x pt))
		(let ((s 0) (ds) (k 0))
		  ;;(exp(e)/ e) sum k!/e^k,k,0,n-1). I know: this is inefficient.
		  (while (< k n)
		    (setq ds (div (ftake 'mfactorial k) (ftake 'mexpt e k)))
	 	 	(setq s (add s ds))
			(setq k (+ 1 k)))
	  	(mul s (div (ftake 'mexpt '$%e e) e))))
	(t (ftake '%expintegral_ei e))))
(setf (gethash '%expintegral_ei *asymptotic-expansion-hash*) #'expintegral-ei-asymptotic)	
	  
;; See https://dlmf.nist.gov/6.12. Let's triple check for a Ei vs E1 flub.
(defun expintegral-e1-asymptotic (e x pt n)
	(let ((s 0) (ds) (k 0))
	  (setq e (first e))
	  (cond ((eq '$inf ($limit e x pt))
	 	     ;;(exp(e)/ e) sum k!/e^k,k,0,n-1). I know: this is inefficient.
		     (while (< k n)
	 	       (setq ds (div (mul (ftake 'mexpt -1 k) (ftake 'mfactorial k)) (ftake 'mexpt e k)))
	  	   	   (setq s (add s ds))
			   (setq k (+ 1 k)))
	 	      (mul s (div (ftake 'mexpt '$%e e) e)))
		   (t (ftake '%expintegral_e1 e)))))
(setf (gethash '%expintegral_e1 *asymptotic-expansion-hash*) #'expintegral-e1-asymptotic)

;; Return a truncated Poincaré-Type expansion (Stirling approximation) 
;; for gamma(e). Reference: http://dlmf.nist.gov/5.11.E1. 
(defun gamma-asymptotic (e x pt n)
	(let ((s 0) ($zerobern t) (ds) (k 1) (xxx)) ;tricky setting for $zerobern
	    (setq e (first e))
		(setq e (asymptotic-expansion e x pt n))
		(setq xxx ($limit e x pt))
	    (cond ((eq '$inf xxx)
			    (while (<= k n)
			        (setq ds (div ($bern (mul 2 k))
		                       (mul (mul 2 k) (sub (mul 2 k) 1)
							   (ftake 'mexpt e (sub (mul 2 k) 1)))))
		            (setq k (+ 1 k))					   
		            (setq s (add s ds)))
	            (mul 
				    (ftake 'mexpt '$%e s)
				   	(ftake 'mexpt (mul 2 '$%pi) (div 1 2))
	                (ftake 'mexpt e (add e (div -1 2)))
		            (ftake 'mexpt '$%e (mul -1 e))))
			  (t (ftake '%gamma e))))) ;give up			 
(setf (gethash '%gamma *asymptotic-expansion-hash*) #'gamma-asymptotic)

(defun mfactorial-asymptotic (e x pt n)
	(let ((fn (gethash '%gamma *asymptotic-expansion-hash*)))
       (funcall fn (list (add 1 (car e))) x pt n)))
(setf (gethash 'mfactorial *asymptotic-expansion-hash*) #'mfactorial-asymptotic)

;; For the case of non integer s, see the comment in specfun.lisp about the 
;; truncation value.

;; For positive integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0003/
;; For negative integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0001/

;; Maybe I should paste this code into li-asymptotic-expansion. But I don't think
;; that Maxima routes the minf case through li-asymptotic-expansion...
(defun polylogarithm-asymptotic (e x pt n)
	(let ((s (first e)) (z (second e)) (nn) (xxx) (k 1) (acc 0))
	   (setq z (asymptotic-expansion z x pt n))
	   (setq xxx ($limit z x pt))
       ;only handle explicit numeric order
	   (cond ((and (integerp s) (> s 0) (or (eq '$inf xxx) (eq '$minf xxx)))
	           (while (<= k n)
			    (setq acc (add acc (div 1 (mul (ftake 'mexpt k s) (ftake 'mexpt z k)))))
				(setq k (+ k 1)))
			  (add
			    (mul (ftake 'mexpt -1 (sub s 1)) acc)	 
	   		  	(mul 
			   	  -1
	        		 (ftake 'mexpt (mul 2 '$%pi '$%i) s)
	   		 		 ($bernpoly (add (div 1 2) 
				  	  (div (ftake '%log (mul -1 z)) (mul 2 '$%pi '$%i))) s)
					(div 1 (ftake 'mfactorial s)))))
			 
			 ((and (integerp s) (> 0 s) (or (eq '$inf xxx) (eq '$minf xxx)))
			    (setq s (- s))
			    (while (<= k n)
			      (setq acc (add acc (div (ftake 'mexpt k s) (ftake 'mexpt z k))))
			  	  (setq k (+ k 1)))
				(mul (ftake 'mexpt -1 (- s 1)) acc))

	         ((and ($ratnump s) (or (eq '$inf xxx) (eq '$minf xxx))) ;really?
			   (setq nn (min (mfuncall '$floor (div s 2)) n))
	           (li-asymptotic-expansion nn s z))
			(t (subfunmake '$li (list s) (list z))))))
(setf (gethash '$li *asymptotic-expansion-hash*) #'polylogarithm-asymptotic)

;; See https://en.wikipedia.org/wiki/Polygamma_function#Asymptotic_expansion 
(defun psi-asymptotic (e x pt n)
	(let ((s 0) (k 0) ($zerobern t) (ds) (xxx) (m) (z))
		(setq m (car e))
	    (setq z (cadr e))
		(setq xxx ($limit z x pt))
		;(mtell "m = ~M ~% z = ~M xxx = ~M ~%~%" m z xxx)
		(cond ((and (eq '$inf xxx) (integerp m) (>= m 1))
				 (while (< k n)
					(setq ds (mul (div (ftake 'mfactorial (add k m -1))
				                       (ftake 'mfactorial k)) 
				                  (div ($bern k) (ftake 'mexpt z (add k m)))))
					(setq k (+ k 1))
					(setq s (add s ds)))
		         (mul (ftake 'mexpt -1 (add m 1)) s))
              ((and (eq '$inf xxx) (eql m 0))
			  	;log(z)-sum(bern(k)/(k*z^k),k,1,n)
			    (setq k 1)
				(while (< k n)
					(setq ds (div ($bern k) (mul k (ftake 'mexpt z k))))
				    (setq s (add s ds)))
				(sub (ftake '%log z) s))	
			  (t (subfunmake '$psi (list m) (list z))))))		 
(setf (gethash '$psi *asymptotic-expansion-hash*) #'psi-asymptotic)

;; See http://dlmf.nist.gov/7.11.E2. Missing the z --> -inf case.
(defun erfc-asymptotic (z x pt n)
	(setq z (car z))
	(let ((s 0) (ds (div 1 z)) (k 0) (zz (mul 2 z z)) (xxx))
	  (setq xxx ($limit z x pt))
	  (cond ((eq '$inf xxx)
			  (while (< k n)
				 (setq s (add s ds))
				 (setq ds (div (mul ds -1 (add 1 (* 2 k))) zz))
				 (setq k (+ k 1)))
			  (mul (ftake 'mexpt '$%e (mul -1 z z)) s (div 1 (ftake 'mexpt '$%pi (div 1 2)))))
		    ((eq '$minf xxx)
			  (while (< k n)
				 (setq s (add s ds))
				 (setq ds (div (mul ds -1 (add 1 (* 2 k))) zz))
				 (setq k (+ k 1)))
				(sub 2 (mul (ftake 'mexpt '$%e (mul -1 z z)) s (div 1 (ftake 'mexpt '$%pi (div 1 2)))))) 
		  (t (ftake '%erfc z)))))		
;(setf (gethash '%erfc *asymptotic-expansion-hash*) #'erfc-asymptotic)

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-expansion-hash*.
(defun erf-asymptotic (z x pt n)
	(let ((fn (gethash '%erfc *asymptotic-expansion-hash*)) (xxx))
	     (setq xxx ($limit (first z) x pt))
		 (cond ((or (eq '$inf xxx) (eq '$minf xxx))
				  (sub 1 (funcall fn z x pt n)))
			   (t (ftake '%erf (first z))))))
;(setf (gethash '%erf *asymptotic-expansion-hash*) #'erf-asymptotic)	

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i  

(defun gamma-incomplete-asymptotic (e x pt n)
	(let ((aaa (first e)) (z (second e)) (s 0) (ds) (k 0) (xxx))
	    (setq z (maxima-substitute '$zeroa 'epsilon z))
		(setq z (maxima-substitute '$inf 'prin-inf z))
		;(setq z ($limit z))
		(setq xxx ($limit z x pt))
		;(mtell "a = ~M ~% z = ~M ~% xxx = ~M ~%" a z xxx)
		;;  z--> inf or z --> -inf and a is freeof x
		;; This should be (and (or (eq '$inf xxx) (eq '$minf xxx))
		;; But doing so exposes a bug in 
		;;   integrate(x*sin(x)*exp(-x^2),x,minf,inf)
		;; that is due to a noncontinuous antiderivative that Maxima
		;; doesn't detect.
		(cond ((and (or (eq '$minf xxx) (eq '$inf xxx)) (freeof x aaa))
		         (while (< k n)
				 	(setq ds (div (mul (ftake 'mexpt -1 k) (ftake '$pochhammer (sub 1 aaa) k))
								  (ftake 'mexpt z k)))
				    (setq s (add s ds))
				    (setq k (+ k 1)))
				 ;; return z^(a-1)*exp(-z)*s
				 (mul (ftake 'mexpt z (sub aaa 1)) (ftake 'mexpt '$%e (mul -1 z)) s))	
              (t (ftake '%gamma_incomplete aaa z)))))
;(setf (gethash '%gamma_incomplete *asymptotic-expansion-hash*) #'gamma-incomplete-asymptotic)		

;; See http://dlmf.nist.gov/10.17.E3. We could also do the large order case?
(defun bessel-j-asymptotic (e x pt n)
	(let ((v (car e)) (z (cadr e)) (ω) (k 0) (a) (b) (sc 0) (cc 0))
	    (cond ((eq '$inf ($limit z x pt))
				(setq ω (add z (div (mul '$%pi v) -2) (div '$%pi -4)))
				(setq a (sub (div 1 2) v))
				(setq b (add (div 1 2) v))
				(labels ((fn (k a b) ;  (1/2-v)_k (1/2+v)_k / ((-2)^k k!)
				     (div
		   	 		 	(mul (ftake '$pochhammer a k) 
				 			 (ftake '$pochhammer b k))
						(mul (ftake 'mexpt -2 k) 
							 (ftake 'mfactorial k)))))	 
		(while (< k n)
			(setq cc (add cc (mul (ftake 'mexpt -1 k) 
			                      (div (fn (* 2 k) a b) (ftake 'mexpt z (* 2 k))))))
			(setq sc (add sc (mul (ftake 'mexpt -1 k))
			                      (div (fn (+ 1 (* 2 k)) a b) (ftake 'mexpt z (+ 1 (* 2 k))))))
			(incf k))
		(mul 
		   (ftake 'mexpt (div 2 (mul '$%pi x)) (div 1 2))
		   (sub (mul cc (ftake '%cos ω)) (mul sc (ftake '%sin ω))))))
		(t (ftake '%bessel_j v x)))))   
(setf (gethash '%bessel_j *asymptotic-expansion-hash*) #'bessel-j-asymptotic)	

;; See http://dlmf.nist.gov/10.40.E2. We could also do the large order case?
(defun bessel-k-asymptotic (e x pt n)
	(let ((v (car e)) (z (cadr e)) (k 0) (a) (b) (cc 0))
	    (cond ((eq '$inf ($limit z x pt))
				(setq a (sub (div 1 2) v))
				(setq b (add (div 1 2) v))
				(labels ((fn (k a b) ; (1/2-v)_k (1/2+v)_k / ((-2)^k k!)
				     (div
		   	 		 	(mul (ftake '$pochhammer a k) 
				 			 (ftake '$pochhammer b k))
						(mul (ftake 'mexpt -2 k) 
							 (ftake 'mfactorial k)))))	 
		(while (< k n)
			(setq cc (add cc (div (fn k a b) (ftake 'mexpt z k))))
			(incf k))
		(mul 
		   (ftake 'mexpt (div '$%pi (mul 2 z)) (div 1 2)) ;sqrt(pi/(2z))
		   (ftake 'mexpt '$%e (mul -1 z) ;exp(-z)
		   cc))))
		(t (ftake '%bessel_k v x)))))   
(setf (gethash '%bessel_k *asymptotic-expansion-hash*) #'bessel-k-asymptotic)	

;; Is this worthwhile? Does it fix any bugs? Does it allow more limits to be
;; evaluated?
(defun atan-asymptotic (e x pt n)
    (setq e (car e))
	(let ((xxx ($limit e x pt))) ;try $limit, not limit
	  ;;; (mtell "e = ~M ~% xxx = ~M ~%" e xxx)
	   (cond ((and (eq xxx '$inf))
	          (unwind-protect 
			    (progn
           		   (mfuncall '$assume (ftake 'mlessp *big* x))
	   		       ($ratdisrep ($taylor (ftake '%atan e) x '$inf n)))
				(mfuncall '$forget (ftake 'mlessp *big* x))))   
			 (t (ftake '%atan e)))))
(setf (gethash '%atan *asymptotic-expansion-hash*) #'atan-asymptotic)

(defun conjugate-asymptotic (e x pt n)
	(setq e (car e))
   	(let ((xxx ($limit e x pt))) ;try $limit, not limit
		(if (eq xxx '$inf)
          (ftake '$conjugate (asymptotic-expansion (cadr e) x pt n))
		  (ftake '$conjugate e))))
(setf (gethash '$conjugate *asymptotic-expansion-hash*) #'conjugate-asymptotic)

(defun asin-asymptotic (e x pt n)
  (setq e (car e))
  (let ((xxx ($limit e x pt))) ;try $limit, not limit
	(setq e (ftake '%asin e))
	(if (eq xxx '$inf)
		($ratdisrep ($taylor e x '$inf n)) e)))
;(setf (gethash '%asin *asymptotic-expansion-hash*) #'asin-asymptotic)

(defun acos-asymptotic (e x pt n)
  (setq e (car e))
  (let ((xxx ($limit e x pt))) ;try $limit, not limit
	(setq e (ftake '%acos e))
	(if (eq xxx '$inf)
		($ratdisrep ($taylor e x '$inf n)) e)))
(setf (gethash '%acos *asymptotic-expansion-hash*) #'acos-asymptotic)

(defun asinh-asymptotic (e x pt n)
  (setq e (car e))
  (let ((xxx ($limit e x pt))) ;try $limit, not limit
	(setq e (ftake '%asinh e))
	(if (eq xxx '$inf)
		($ratdisrep ($taylor e x '$inf n)) e)))
(setf (gethash '%asinh *asymptotic-expansion-hash*) #'asinh-asymptotic)

(defvar *zztop* nil)
(defun sin-asymptotic (e x pt n)
	(setq e (car e))
	(let ((xxx (limit-catch e x pt)))
	
	 (mtell "e = ~M ; x = ~M ; pt = ~M ; xxx = ~M ~%" e x pt xxx)
	(cond ((and nil (eql 0 (ridofab xxx)) (not (eq e 'epsilon)))
	         (setq xxx ($taylor e x (ridofab pt) n))
			 (mtell "xxx = ~M ~% " xxx)
	        ($ratdisrep (ftake '%sin ($taylor e x (ridofab pt) n))))
         (t
	        (push (ftake 'mlist e x pt xxx) *zztop*)
	        (ftake '%sin e)))))
;(setf (gethash '%sin *asymptotic-expansion-hash*) #'sin-asymptotic)
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

	
