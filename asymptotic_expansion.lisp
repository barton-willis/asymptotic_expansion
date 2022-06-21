;;; Maxima code for finding asymptotic expansions of various functions, including 
;;; erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, polylogarithm, and 
;;; polygamma functions. 

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

;; Consider appending code for {bessel_j, bessel_k,gamma_incomplete}
(in-package :maxima)

;; What special variables did I miss?
(declare-top (special var val lhp?))

;;;;

(defvar *big* (expt 2 107))
(defvar *tiny* (div 1 (expt 2 107)))

;; This function is for internal use in $limit.
(defun gruntz1 (exp var val &rest rest)
   (cond ((> (length rest) 1)
	 (merror (intl:gettext "gruntz: too many arguments; expected just 3 or 4"))))
  (let (($logexpand t) ; gruntz needs $logexpand T
        (newvar (gensym "w"))
	(dir (car rest)))
	(putprop newvar t 'internal); keep var from appearing in questions to user	
    (cond ((eq val '$inf)
	   (setq newvar var))
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
			      (mtell "before: exp = ~M ~%" exp)
	    	      (mfuncall '$assume (ftake 'mlessp 0 'lim-epsilon)) ;0 < lim-epsilon
	    	      (mfuncall '$assume (ftake 'mlessp 'lim-epsilon *tiny*)) ; lim-epsilon < *tiny*
			      (mfuncall '$assume (ftake 'mlessp *big* 'prin-inf)) ; *big* < prin-inf
			      (mfuncall '$assume (ftake 'mlessp 0 '$zeroa)) ; 0 < $zeroa
				  (mfuncall '$assume (ftake 'mlessp '$zerob 0)) ; $zerob < 0
				  (mfuncall '$assume (ftake 'mlessp *big* newvar)) ; *big* < newvar
				  (mfuncall '$activate cntx) ;not sure this is needed			
				  (let ((val '$inf)) ;not sure about
				     (setq exp ($expand exp 0 0)) ;simplify in new context
					 (mtell "after: exp = ~M ~%" exp)	
                     (setq exp (asymptotic-expansion exp newvar '$inf 1));pre-condition
					 (mtell "after2: exp = ~M ~%" exp)
					 (limitinf exp newvar))) ;compute limit
            ($killcontext cntx)))))
;;;;

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

;; Maybe not indented to be a user level function?
(defun $asymptotic_expansion (e x pt n)
	(asymptotic-expansion e x pt n))

;; I'm not sure this is needed--ultimately it dispatches the CL function limit, but
;; first it creates a supercontext, assumes the limit variable is larger than a
;; magic number *big*, and conditions the limit expression using  asymptotic-expansion.

;; I'm not sure that the call to $activate is needed--the user documentation is 
;; clear when it is needed.
(defun limit-toward-infinity (e x)	
	(unwind-protect 
		(let ((cntx ($supcontext)))
			  (progn
	  			  (mfuncall '$assume (ftake 'mgreaterp x *big*))
				  (mfuncall '$activate cntx)
		 	 	  (setq e ($expand e 0 0)) ;simplify in new context
				  (setq e (asymptotic-expansion e x '$inf 1))
				  (limit e x '$inf 'think))
			   ($killcontext cntx))))

;; For experimentation, lets collect all operators that use the default mapping of
;; asymptotic-expansion. Currently running the testsuite, these functions are
;; {conjugate, floor, acos, asinh, atan, bessel_k, cos, gamma_incomplete,
;; log, sin, tan, ^}
(defvar *xxx* nil) 

;; For the expression e, replace various functions (gamma, polylogarithm, and ...)
;; functions with truncated asymptotic (Poincaré) expansions. 
(defun asymptotic-expansion (e x pt n)
	(let (($domain '$complex) (fn nil) (args nil) (lhp? nil))
        ;; Unify dispatching a *asymptotic-expansion-hash* function on both 
		;; subscripted and nonsubscripted functions. For a subscripted
		;; function, args = (append subscripted args, regular args).
        (cond ((and (consp e) (consp (car e)) (eq 'mqapply (caar e)))
                   (setq fn (gethash (subfunname e) *asymptotic-expansion-hash* nil))
                   (setq args (append (subfunsubs e) (subfunargs e))))
	            ((and (consp e) (consp (car e)))
			        (setq fn (gethash (caar e) *asymptotic-expansion-hash* nil))
                    (setq args (cdr e))))
		;(print `(dispatching ,fn))			
		(cond (($mapatom e) e)
			  (fn
				(apply fn (list args x pt n)))
	   	      (t 
			    (push (caar e) *xxx*) ;collect unsupported function names
			    (mfuncall '$map #'(lambda (q) (asymptotic-expansion q x pt n)) e)))))
			
;; For a sum, map asymptotic-expansion onto the summand and sum the result. When
;; the sum vanishes, increase the truncation order and try again. When the order n 
;; reaches a magic number (8), give up and return e. 

;; The first argument e is a CL list of the summand. The second argument is the 
;; limit variable, the third is the point, and the last is the truncation level.

(defvar *zero-case* 0)
(defun mplus-asymptotic (e x pt n)
    (let ((ans))
	    (setq ans (addn (mapcar #'(lambda (s) (asymptotic-expansion s x pt n)) e) t))
        ;(setq ans (sratsimp ans)) ;needed or unneeded?
        (while (and (zerop1 (sratsimp ans)) (< n 8)) ;magic number 8.
			(mtell "Caught a zero case! = ~M ~M ~%" e ans) ;untested!
			(setq *zero-case* (+ 1 *zero-case*))
			(setq n (+ 1 n))
			(setq ans (mplus-asymptotic e x pt n)))
        (if (zerop1 ans) (addn e t) ans))) ;when ans is still zero, sum e and return.
(setf (gethash 'mplus *asymptotic-expansion-hash*) #'mplus-asymptotic)

;; We could use the default of mapping asymptotic-expansion over the 
;; arguments. But this version does a post multiplication 
;; sratsimp. Maybe the sratsimp eliminates a bug?
(defun mtimes-asymptotic (e x pt n)
	(sratsimp (muln (mapcar #'(lambda (s) (asymptotic-expansion s x pt n)) e) t)))
;(setf (gethash 'mtimes *asymptotic-expansion-hash*) #'mtimes-asymptotic)

;; See https://dlmf.nist.gov/6.12.  Let's triple check for a Ei vs E1 flub.
(defun expintegral-ei-asymptotic (e x pt n)
	(setq e (first e))
	(cond ((eq '$inf (limit e x pt 'think))
		(let ((s 0) (ds) (k 0))
		  ;;(exp(e)/ e) sum k!/e^k,k,0,n-1). I know: this is inefficient--I'll fix that.
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
	  (cond ((eq '$inf (limit e x pt 'think))
	 	     ;;(exp(e)/ e) sum k!/e^k,k,0,n-1). I know: this is inefficient--I'll fix that.
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
		;(mtell "n = ~M ~%" n)
		;(setq n 2)
		(setq e (asymptotic-expansion e x pt n))
		(setq xxx (limit e x pt 'think))
	    (cond ((eq '$inf xxx)
			    (while (<= k n)
			        (setq ds (div ($bern (mul 2 k))
		                       (mul (mul 2 k) (sub (mul 2 k) 1)
							   (ftake 'mexpt e (sub (mul 2 k) 1)))))
		            (setq k (+ 1 k))					   
		            (setq s (add s ds)))
	            (mul ($ratdisrep ($taylor (ftake 'mexpt '$%e s) x '$inf n)) ;Taylor uneeded?
	               	(ftake 'mexpt (mul 2 '$%pi) (div 1 2))
	                (ftake 'mexpt e (add e (div -1 2)))
		            (ftake 'mexpt '$%e (mul -1 e))))
              ((and (integerp xxx) (< xxx 0)) ;pole case
			     ($ratdisrep ($taylor e x xxx n)))
			  (t (ftake '%gamma e))))) ;give up			 
(setf (gethash '%gamma *asymptotic-expansion-hash*) #'gamma-asymptotic)

(defun mfactorial-asymptotic (e x pt n)
    (gamma-asymptotic (list (add 1 (first e))) x pt n))
(setf (gethash 'mfactorial *asymptotic-expansion-hash*) #'mfactorial-asymptotic)

;; See the comment in specfun.lisp about the truncation value.

;; For positive integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0003/
;; For negative integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0001/

(defun polylogarithm-asymptotic (e x pt n)
	(let ((s (first e)) (z (second e)) (nn) (xxx) (k 1) (acc 0))
	   (setq z (asymptotic-expansion z x pt n))
	   (setq xxx (limit z x pt 'think))
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
		(setq m (cadr e))
	    (setq z (caddr e))
		(setq xxx (limit z x pt 'think))
		(cond ((and (eq '$inf xxx) (freeof x m))
				(while (< k n)
					(setq ds (mul (div (ftake 'mfactorial (add k m -1))
				                       (ftake 'mfactorial k)) 
				                   (div ($bern k) (ftake 'mexpt z (add k m)))))
					(setq k (+ k 1))
					(setq s (add s ds)))
		        (mul (ftake 'mexpt -1 (add m 1))))
			  (t (subfunmake '$psi (list m) (list z))))))		 
(setf (gethash '$psi *asymptotic-expansion-hash*) #'psi-asymptotic)

;; See http://dlmf.nist.gov/7.11.E2. Missing the z --> -inf case.
(defun erfc-asymptotic (z x pt n)
	(setq z (car z))
	(let ((s 0) (ds (div 1 z)) (k 0) (zz (mul 2 z z)) (xxx))
	  (setq xxx (limit z x pt 'think))
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
	(let ((fn (gethash '%erfc *asymptotic-expansion-hash*))) 
		(sub 1 (funcall fn z x pt n))))
(setf (gethash '%erf *asymptotic-expansion-hash*) #'erf-asymptotic)	

;; Need to include the cases: large a, fixed z; large a, fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i 

;; This causes trouble with integrate(x*exp(-x^2)*sin(x),x,minf,inf). This
;; is a test in rtest_limit_extra.  One cure for the test is to cancel the
;; limit function for gamma_incomplete. But that causes other testsuite
;; failures.

;(defprop %gamma_incomplete nil simplim%function)
(defun gamma-incomplete-asymptotic (e x pt n)
	(let ((a (first e)) (z (second e)) (s 0) (ds) (k 0) (xxx))
		;; z--> infinity, a is freeof x
		(setq xxx (limit z x pt 'think))
		(cond ((and (or (eq '$inf xxx) (eq '$minf xxx)) (freeof x a))
		         (while (< k n)
				 	(setq ds (div (mul (ftake 'mexpt -1 k) (mfuncall '$pochhammer (sub 1 a) k))
								  (ftake 'mexpt z k)))
				    (setq s (add s ds))
				    (setq k (+ k 1)))
				 (mul (ftake 'mexpt z (sub a 1)) (ftake 'mexpt '$%e (mul -1 z)) s))	
              (t (ftake '%gamma_incomplete a z)))))
;(setf (gethash '%gamma_incomplete *asymptotic-expansion-hash*) #'gamma-incomplete-asymptotic)		

(defun bessel-j-asymptotic (e x pt n)
	(let ((v (car e)) (z (cadr e)) (ω) (k 0) (a) (b) (sc 0) (cc 0))
	    (cond ((eq '$inf (limit z x pt 'think))
				(setq ω (add z (div (mul '$%pi v) -2) (div '$%pi -4)))
				(setq a (sub (div 1 2) v))
				(setq b (add (div 1 2) v))
				(labels ((fn (k a b z)
				     (div
		   	 		 	(mul (ftake 'mexpt -1 k)
						     (ftake '$pochhammer a k) 
				 			 (ftake '$pochhammer b k))
						(mul (ftake 'mexpt z k) 
							 (ftake 'mexpt -2 k) 
							 (ftake 'mfactorial k)))))	 
		(while (< k n)
			(setq cc (add cc (fn (* 2 k) a b z)))
			(setq sc (add sc (fn (+ 1 (* 2 k)) a b z)))
			(incf k))
		(mul 
		   (ftake 'mexpt (div 2 (mul '$%pi x)) (div 1 2))
		   (add (mul cc (ftake '%cos ω)) (mul sc (ftake '%sin ω))))))
		(t (ftake '%bessel_j v x)))))   
(setf (gethash '%bessel_j *asymptotic-expansion-hash*) #'bessel-j-asymptotic)		
