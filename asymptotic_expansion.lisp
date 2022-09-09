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

(defun gruntz1 (exp var val &rest rest)
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
  
       (let ((cntx ($supcontext)))
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
				  (let ((val '$inf)) ;not sure about locally setting val?
				     (setq exp (sratsimp exp)) ;simplify in new context
                     (setq exp (asymptotic-expansion exp newvar '$inf 10));pre-condition
					 (limitinf exp newvar))) ;compute & return limit
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
		;; subscripted and nonsubscripted functions. For a subscripted
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
		(setq ans (ftake 'mexpt a b))
		(if (and (integerp a) (> a 0)) ($radcan ans) ans)))
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
      (cond ((eq t (mgrp xxx 0)) ;new!
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

;; For the case of noninteger s, see the comment in specfun.lisp about the 
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
		  (t (ftake '%erfc z)))))		
(setf (gethash '%erfc *asymptotic-expansion-hash*) #'erfc-asymptotic)

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-expansion-hash*.
(defun erf-asymptotic (z x pt n)
	(let ((fn (gethash '%erfc *asymptotic-expansion-hash*)) (xxx))
	     (setq xxx ($limit (first z) x pt))
		 (cond ((eq '$inf xxx)
				  (sub 1 (funcall fn z x pt n)))
			   (t (ftake '%erf (first z))))))
(setf (gethash '%erf *asymptotic-expansion-hash*) #'erf-asymptotic)	

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i  

(defun gamma-incomplete-asymptotic (e x pt n)
	(let ((a (first e)) (z (second e)) (s 0) (ds) (k 0) (xxx))
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
		(cond ((and (or (eq '$inf xxx)) (freeof x a))
		         (while (< k n)
				 	(setq ds (div (mul (ftake 'mexpt -1 k) (ftake '$pochhammer (sub 1 a) k))
								  (ftake 'mexpt z k)))
				    (setq s (add s ds))
				    (setq k (+ k 1)))
				 ;; return z^(a-1)*exp(-z)*s
				 (mul (ftake 'mexpt z (sub a 1)) (ftake 'mexpt '$%e (mul -1 z)) s))	
              (t (ftake '%gamma_incomplete a z)))))
(setf (gethash '%gamma_incomplete *asymptotic-expansion-hash*) #'gamma-incomplete-asymptotic)		

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
(setf (gethash '%asin *asymptotic-expansion-hash*) #'asin-asymptotic)

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

;; Dispatch Taylor, but recurse on the order until either the order 
;; reaches 107 or the Taylor polynomial is nonzero. When Taylor either
;; fails to find a nonzero Taylor polynomial, return nil.

;; This recursion on the order attempts to handle limits such as 
;; tlimit(2^n/n^5, n, inf) correctly. Initially, the order n needs to be 
;; one or greater. 

;; We set up a reasonable environment for calling taylor. Maybe I went overboard.
(defun my-taylor (e x pt n)
	(let ((ee 0) 
	      (silent-taylor-flag t) 
	      ($taylordepth 8)
		  ($taylor_logexpand nil)
		  ($maxtaylororder t)
		  ($taylor_truncate_polynomials nil)
		  ($taylor_simplifier #'sratsimp))
		 (setq n (max 1 n)) ;make sure n >= 1
		 (while (and (eq t (meqp ee 0)) (< n 107))
			(setq ee (catch 'taylor-catch ($taylor e x pt n)))
			(setq n (* 2 n)))
		(if (eq t (meqp ee 0)) nil ee)))

;; Previously when the taylor series failed, there was code for deciding
;; whether to call limit1 or simplimit. The choice depended on *i* and the 
;; main operator of the expression. I think all this logical is unnecessary.
;; We can just call limit1. Doing so makes *i* unused, but since *i* is special, 
;; it cannot be ignored.

;; There is no reason for initially asking for a $lhospitallim order
;; taylor series, but it's a tradition and in the user documentation.
(defun taylim (e x pt *i*)
	(let ((et) ($algebraic t))
	  (when (eq pt '$inf) 
		 (setq e (asymptotic-expansion e x pt $lhospitallim)))
	  (setq et (my-taylor e x (ridofab pt) $lhospitallim))
	  (cond (et 
	         (let ((taylored t) (limit-using-taylor nil))
			   (limit ($ratdisrep et) x pt 'think)))
			(t (limit1 e x pt)))))
		
