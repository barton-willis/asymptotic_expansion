;;; Maxima code for finding asymptotic expansions of various functions, including 
;;; bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, 
;;; polylogarithm, and polygamma functions. 

;;; The purpose of this code is for computing limits. Specifically
;;; limit(e,x,pt) = limit(asymptotic-expansion(e,x,pt),x,pt) is supposed to be
;;; an identity. Possibly asymptotic-expansion could be promoted to a user level 
;;; function, but for now it isn't intended to be a user level function.

;;; Copyright (C) 2022, 2023 Barton Willis
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
(declare-top (special var val lhp? taylored silent-taylor-flag limit
   $taylordepth $taylor_logexpand $maxtaylororder $taylor_simplifer))

; Define *big* and *tiny* to be "big" and "tiny" numbers, respectively. There
;; is no particular logic behind the choice *big* = 2^107 and *tiny* = 1/2^107.
(defvar *big* (expt 2 107))
(defvar *tiny* (div 1 (expt 2 107)))

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
(defmfun $asymptotic_expansion (e x pt n)
	(asymptotic-expansion e x pt n))

;; For experimentation, let's collect all operators that don't have a specialized 
;; asymptotic expansion function in a hashtable *xxx*. The function $missing
;; prints a report on these missing operators. Similarly collect the operators
;; that are used. Eventually remove this code. 

#|
Currently, running the testsuite (including share), the result is

Missing operators:
tan 1618
cos 14436
derivative 6
floor 32
sin 16970

Used operators:
log 1767
atan 166
conjugate 2
^ 32490
* 21094
psi 2
li 94
abs 864
gamma_incomplete 427
bessel_j 1
bessel_k 1
+ 7548
factorial 38
erf 27
expintegral_ei 12
asinh 8

|#

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
		  ($taylor_logexpand t)
		  ;($domain '$complex) ;extra not sure about this
		  ;($m1pbranch t) ;not sure about this
		  ;($algebraic t)
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
        (while (and (< n 8) (zerop1 (sratsimp ans))) ;magic number 8.
			(incf *zero-case* 1)
			(incf n)
			(setq ans (mplus-asymptotic e x pt n)))
         (if (zerop1 ans) (addn e t) ans))) ;when ans is still zero, sum e and return
(setf (gethash 'mplus *asymptotic-expansion-hash*) #'mplus-asymptotic)

;; Return the product of the result of mapping asymptotic-expansion over the terms 
;; in the CL list e.
(defun mtimes-asymptotic (e x pt n)
	(muln (mapcar #'(lambda (s) (asymptotic-expansion s x pt n)) e) t))
(setf (gethash 'mtimes *asymptotic-expansion-hash*) #'mtimes-asymptotic)

;; Map asymptotic-expansion onto the arguments of mexpt.
(defun mexpt-asymptotic (e x pt n)
	(ftake 'mexpt 
		    (asymptotic-expansion (car e) x pt n)
			(asymptotic-expansion (cadr e) x pt n)))
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
	    (setq e (sratsimp (car e)))
		(setq e (asymptotic-expansion e x pt n))
		(when (eql pt 0)
			(setq pt '$zeroa))
		(setq xxx (let ((preserve-direction t)) (limit e x pt 'think)))
		;; Need to check if this is OK for infinity & minf
	    (cond ((or (eq '$inf xxx) (eq '$infinity xxx) (eq '$minf xxx))
		        (setq e (asymptotic-expansion e x pt n))
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

                ((or (eq xxx '$zeroa) (zerop2 xxx))
		         (setq e (ftake '%gamma e))
		 	     ($ratdisrep (tlimit-taylor e x (ridofab pt) n)))
			  (t (ftake '%gamma e))))) ;give up		

(setf (gethash '%gamma *asymptotic-expansion-hash*) 'gamma-asymptotic)

(defun mfactorial-asymptotic (e x pt n)
	(let ((fn (gethash '%gamma *asymptotic-expansion-hash*)))
       (funcall fn (list (add 1 (car e))) x pt n)))
(setf (gethash 'mfactorial *asymptotic-expansion-hash*) #'mfactorial-asymptotic)

;; For the case of non integer s, see the comment in specfn.lisp about the 
;; truncation value.

;; For positive integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0003/
;; For negative integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0001/

;; Maybe I should paste this code into li-asymptotic-expansion. But I don't think
;; that Maxima routes the minf case through li-asymptotic-expansion...
(defun polylogarithm-asymptotic (e x pt n)
	(let (($numer nil) (s (first e)) (z (second e)) (nn) (xxx) (k 1) (acc 0))
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
(setf (gethash '$li *asymptotic-expansion-hash*) 'polylogarithm-asymptotic)

;; See https://en.wikipedia.org/wiki/Polygamma_function#Asymptotic_expansion 
(defun psi-asymptotic (e x pt n)
	(let ((s 0) (k 0) ($zerobern t) (ds) (xxx) (m) (z))
		(setq m (car e))
	    (setq z (cadr e))
		(setq xxx ($limit z x pt))
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
;; Running the testsuite, this causes an asksign 
(defun erfc-asymptotic (z x pt n)
	(setq z (car z))
	(let ((s 0) (ds (div 1 z)) (k 0) (zz (mul 2 z z)) (xxx))
	  (setq xxx ($limit z x pt))
	  ;(setq xxx (limit z x pt 'think))
	  ;; The infinity clause is likely bogus!
	  (cond ((or (eq '$inf xxx) (eq '$infinity xxx))
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
(setf (gethash '%erfc *asymptotic-expansion-hash*) #'erfc-asymptotic)

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-expansion-hash*.

;; Running the testsuite, this causes an asksign on integrate( erf(x+a)-erf(x-a), x, minf, inf)
;; (in rtestint).  For now, let's turn this off
(defun erf-asymptotic (z x pt n)
	(let ((fn (gethash '%erfc *asymptotic-expansion-hash*)) (xxx))
	    (setq z (first z))
	     (setq xxx ($limit z x pt))
		 (cond ((or (eq '$inf xxx) (eq '$infinity xxx) (eq '$minf xxx))
				  (sub 1 (funcall fn (list z) x pt n)))
			   (t (ftake '%erf z)))))
(setf (gethash '%erf *asymptotic-expansion-hash*) #'erf-asymptotic)	

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i
(defun gamma-incomplete-asymptotic (e x pt n)
	(let* ((aaa (first e)) (z (second e)) (xxx (limit z x pt 'think)))
		(cond 
          ;; Case 1: Asymptotic expansion when z -> +/- inf and aaa is free of x
          ;; For the series, see http://dlmf.nist.gov/8.11.i
		  ((and (or (eq '$inf xxx) (eq '$minf xxx)) (freeof x aaa))
		         (let ((f 1) (s 0))
		           (dotimes (k n)
				      (setq s (add s f))
                      (setq f (mul f (div (add aaa -1 (- k)) z))))
				 ;; return z^(a-1)*exp(-z)*s
				 (mul (ftake 'mexpt z (sub aaa 1)) (ftake 'mexpt '$%e (mul -1 z)) s)))
           ;; Case 2: Asymptotic expansion when z -> 0, aaa integer, and aaa <= 0
		   ;; For the series, see http://dlmf.nist.gov/8.4.E15
		   ((and (zerop2 xxx) (integerp aaa) (>= 0 aaa))
		      (let ((s 0))
		      (flet ((fn (k) (if (eql (add k aaa) 0) 
			                        0 
									(div (power (neg z) k) (mul (ftake 'mfactorial k) (add k aaa))))))
					(dotimes (k n)
						(setq s (add s (fn k))))
					
					(sub (mul
					       (div (ftake 'mexpt -1 (neg aaa)) (ftake 'mfactorial (neg aaa)))
					       (sub 
					         (simplifya (subfunmake '$psi (list 0) (list (add (neg aaa) 1))) nil)
						     (ftake '%log z)))
						 (mul (ftake 'mexpt z (neg aaa)) s)))))
	       ;; Case 3: fall back			
           (t (ftake '%gamma_incomplete aaa z)))))
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

