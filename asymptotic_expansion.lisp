;;; Maxima code for finding asymptotic expansions of various functions, including 
;;; bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, 
;;; polylogarithm, and polygamma functions. 

;;; The purpose of this code is for computing limits. Specifically
;;; limit(e,x,pt) = limit(asymptotic-rewrite(e,x,pt),x,pt) is supposed to be
;;; an identity. Possibly asymptotic-rewrite could be promoted to a user level 
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
(declare-top (special preserve-direction var val lhp?))

(defun limit-at (arg x pt)
"Normalize directional limit points and call $limit. PT may be an ordinary limit point or one of 
 the directional markers $zerob or $zeroa." 
	(cond ((eq pt '$zerob) ($limit arg x 0 '$minus))
		  ((eq pt '$zeroa) ($limit arg x 0 '$plus))
		  (t ($limit arg x pt))))

(defmvar *asymptotic-max-order* 16)

;; Hash table: key is a function name (for example, %gamma) with the 
;; corresponding value a CL function that produces an asymptotic 
;; expansion for the function with that key. Each function has
;; the signature fn(e,x,pt,n), where e is a CL list of the arguments
;; of the function being expanded, x is the limit variable, pt is 
;; the limit point, and n is the truncation order. When these functions
;; cannot find the expansion, the returned value is a nounform
;; for the function.
(defparameter *asymptotic-rewrite-hash* (make-hash-table :test #'eq :size 16))

(defmacro def-asymptotic-rewrite-handler (op args &body body)
  "Define a function OP-ASYMPTOTIC and register it in *asymptotic-rewrite-hash*.
   OP is a Maxima operator symbol such as MTIMES or MPLUS."
  (let* ((fname (intern (format nil "~A-ASYMPTOTIC" op)))
         (op-sym (if (symbolp op) op (intern (string op)))))
    `(progn
       (defun ,fname ,args
         ,@body)
       (setf (gethash ',op-sym *asymptotic-rewrite-hash*)
             ',fname)
       ',fname)))

;; Not intended to be a user level function.
(defmfun $asymptotic_rewrite (e x pt n)
    (let ((LHP? nil)) ;not sure about this.
	  (asymptotic-rewrite e x pt n)))

;; For the expression e, replace various functions (gamma, polylogarithm, and ...)
;; functions with a truncated asymptotic (Poincaré) expansions. We walk through
;; the expression tree and use hashtable to find operators with a
;; specialized function for an asymptotic expansion. When we find such an
;; operator, dispatch the function from the hashtable.

;; This code is supposed to preserve limits. By this I mean
;; limit(XXX,x,pt) = limit(YYY,x,pt), where YYY is the result
;; of applying asymptotic-rewrite to XXX.



(defun asymptotic-rewrite-dispatch (e)
 "Return the asymptotic rewrite handler and normalized argument list for E.

If E represents a function call with a registered asymptotic rewrite
handler in *ASYMPTOTIC-REWRITE-HASH*, return two values:
  1. The handler function.
  2. The argument list passed to that handler.
For ordinary function calls, the argument list is simply (cdr e).

For subscripted function calls (MQAPPLY forms), the argument list is
normalized to

  (append (subfunsubs e) (subfunargs e))

so that subscripted and non-subscripted functions share a common
dispatch interface.

If no handler is registered for E, return NIL NIL."
  (cond
    ;; Subscripted function
    ((and (consp e)
          (consp (car e))
          (eq 'mqapply (caar e)))
     (values
       (gethash (subfunname e)
                *asymptotic-rewrite-hash*)
       (append (subfunsubs e)
               (subfunargs e))))

    ;; Ordinary function
    ((and (consp e)
          (consp (car e)))
     (values
       (gethash (caar e)
                *asymptotic-rewrite-hash*)
       (cdr e)))

    ;; No dispatch
    (t
     (values nil nil))))

(defun asymptotic-rewrite (e x pt n)
  "Perform a recursive rewrite of the expression tree, applying a handler
   when available and otherwise rewriting subexpressions."
  ;; Atoms are unchanged
  (cond
    ;; Mapatoms are unchanged
    (($mapatom e)
     e)
    ;; Special-case MPLUS: rewrite its summands using a dedicated handler--when cancellation happens, the mplus
	;; handler increases the order and tries again, stopping when the order reaches *asymptotic-max-order*.
	;; When that happens, the code gives up and simply adds the members of e.
    ((mplusp e)
     (asymptotic-rewrite-mplus (cdr e) x pt n))

    ;; General case: dispatch to handler or recursively rewrite arguments
    (t
     (multiple-value-bind (fn args)
         (asymptotic-rewrite-dispatch e)
       ;; Rewrite each argument at order n
       (let ((rew-args (mapcar (lambda (s) (asymptotic-rewrite s x pt n)) args)))
         (if fn
             ;; Handler exists → call it with rewritten args
             (apply fn (list rew-args x pt n))
             ;; No handler → rebuild expression with rewritten args
             (fapply (caar e) rew-args)))))))

;; For a sum, map asymptotic-rewrite onto the summand and sum the result. When
;; the sum vanishes, increase the truncation order and try again. When the order n 
;; reaches a magic number (8), give up and return e. 

;; The first argument e is a CL list of the summand. The second argument is the 
;; limit variable, the third is the point, and the last is the truncation level.
(defun asymptotic-rewrite-mplus (e x pt n)
  (let ((ans (fapply 'mplus (mapcar #'(lambda (s) (asymptotic-rewrite s x pt n)) e))))
    (cond ((zerop1 ans)
           ;; Try higher-order expansion; if that fails, return the sum of the list e.
           (if (< n *asymptotic-max-order*)
               (asymptotic-rewrite (fapply 'mplus e) x pt (1+ n))
			   (fapply 'mplus e)))
          (t ans))))

;; See https://dlmf.nist.gov/6.12.  Let's triple check for a Ei vs E1 flub.
(def-asymptotic-rewrite-handler %expintegral_ei (ee x pt n)
    (let* ((e (car ee)) (lim (limit-at e x pt)))
	(cond ((eq '$inf lim)
		(let ((s 0) (ds) (k 0))
		  ;;(exp(-e)/ e) sum(k!/e^k,k,0,n-1). I know: this is inefficient.
		  (while (< k (max n 2))
		    (setq ds (div (ftake 'mfactorial k) (ftake 'mexpt e k)))
	 	 	(setq s (add s ds))
			(setq k (+ 1 k)))
	  	(mul s (div (ftake 'mexpt '$%e e) e))))

		;; see http://dlmf.nist.gov/6.6.E1
		((zerop2 lim)
		  (let ((acc (add '$%gamma (ftake '%log e))) (k 0))
		    ;; %gamma + log(e) + sum(e^k / (k * k!),k,1,n). Again, I know that this code
			;; is a bit inefficient.
		  	(while (< k n)
			    (incf k 1)
				(setq acc (add acc (div (ftake 'mexpt e k) (mul k (ftake 'mfactorial k))))))
			acc))
	(t (ftake '%expintegral_ei ee)))))
	  
;; See https://dlmf.nist.gov/6.12. Let's triple check for a Ei vs E1 flub.
(defun expintegral-e1-asymptotic (e x pt n)
	(let ((s 0) (ds) (k 0))
	  (setq e (first e))
	  (cond ((eq '$inf (limit-at e x pt))
	 	     ;;(exp(e)/ e) sum k!/e^k,k,0,n-1). I know: this is inefficient.
		     (while (< k n)
	 	       (setq ds (div (mul (ftake 'mexpt -1 k) (ftake 'mfactorial k)) (ftake 'mexpt e k)))
	  	   	   (setq s (add s ds))
			   (setq k (+ 1 k)))
	 	      (mul s (div (ftake 'mexpt '$%e e) e)))
		   (t (ftake '%expintegral_e1 e)))))
(setf (gethash '%expintegral_e1 *asymptotic-rewrite-hash*) #'expintegral-e1-asymptotic)

;; Return a truncated Poincaré-Type expansion (Stirling approximation) 
;; for gamma(e). Reference: http://dlmf.nist.gov/5.11.E1. 
(def-asymptotic-rewrite-handler %gamma (e x pt n)
	(let* ((s 0) 
	       ($zerobern t) ; We want bern(even integer) = 0
	       (ds) (k 1)
		   (arg (car e))
		   (lim (limit-at arg x pt)))
		(when (eql lim 0)
			(setq lim (zero-fixup arg x pt)))
		;; Need to check if this is OK for infinity & minf
	    (cond ((or (eq '$inf lim) (and (eq '$infinity lim) (off-negative-real-axisp arg))) ; not sure about minf?
			    (while (<= k n)
			        (setq ds (div ($bern (mul 2 k))
		                       (mul (* 2 k) (- (* 2 k) 1)
							   (ftake 'mexpt arg (- (* 2 k) 1)))))
		            (setq k (+ 1 k))					   
		            (setq s (add s ds)))
	            (mul 
				    (ftake 'mexpt '$%e s)
				   	(ftake 'mexpt (mul 2 '$%pi) (div 1 2))
	                (ftake 'mexpt arg (add arg (div -1 2)))
		            (ftake 'mexpt '$%e (mul -1 arg))))

                ((or (eq lim '$zeroa) (zerop2 lim))
		         (setq arg (ftake '%gamma arg))
		 	     (resimplify ($ratdisrep (tlimit-taylor arg x (ridofab pt) n))))
			  (t (ftake '%gamma arg))))) ;give up		

(def-asymptotic-rewrite-handler mfactorial (e x pt n)
	(let ((fn (gethash '%gamma *asymptotic-rewrite-hash*)))
	   (if fn
            (funcall fn (list (add 1 (car e))) x pt n)
			(ftake 'mfactorial (car e)))))

;; For the case of non integer s, see the comment in specfn.lisp about the 
;; truncation value.

;; For positive integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0003/
;; For negative integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0001/

;; Maybe I should paste this code into li-asymptotic-expansion. But I don't think
;; that Maxima routes the minf case through li-asymptotic-expansion...
(defun polylogarithm-asymptotic-rewrite (e x pt n)
	(let (($numer nil) (s (first e)) (z (second e)) (nn) (xxx) (k 1) (acc 0))
	   (setq xxx (limit-at z x pt))
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
(setf (gethash '$li *asymptotic-rewrite-hash*) 'polylogarithm-asymptotic-rewrite)

(defun polygamma-reflection (m z)
    ;; psi^(m)(z) = (-1)^m psi^(m)(1-z)- %pi * d^m/dz^m cot(pi z)
	(let* ((q (gensym)) (g (maxima-substitute z q ($diff (ftake '%cot (mul '$%pi q)) q m))))
     (sub
       (mul (ftake 'mexpt -1 m)
            (subfunmake '$psi (list m) (list (sub 1 z))))
     (mul '$%pi g))))

;; See https://en.wikipedia.org/wiki/Polygamma_function#Asymptotic_expansion 
(defun psi-asymptotic-rewrite (e x pt n)
	(let* ((s 0) (k 0) ($zerobern t) (ds) (m (car e))
	       (arg (resimplify (cadr e)))
		   (tay-arg (tlimit-taylor arg x (ridofab pt) n))
		   (lim (limit arg x pt 'think)))
        (if tay-arg
			(setq arg tay-arg)
			(return-from psi-asymptotic-rewrite  (subfunmake '$psi (list m) (list arg)))) 
		(cond ((and (eq '$inf lim) (integerp m) (>= m 1))
				 (while (< k n)
					(setq ds (mul (div (ftake 'mfactorial (add k m -1))
				                       (ftake 'mfactorial k)) 
				                  (div ($bern k) (ftake 'mexpt arg (add k m)))))
					(incf k)
					(setq s (add s ds)))
		         (mul (ftake 'mexpt -1 (add m 1)) s))

			  ((and (integerp (ridofab lim)) (eq t (mgqp 0 lim)) (integerp m))
			    (let* ((w (gensym))
                       (asym ($ratdisrep ($taylor (subfunmake '$psi (list m) (list w)) w (ridofab lim) n))))
				  (resimplify (maxima-substitute arg w asym))))

              ;; When lim is minf and the order m is an integer, use the polygamma reflection
			  ;; formula and then dispatch asymptotic-rewrite. If we need extra protection against
			  ;; an infinite loop, we could try checking that limit(cadr(z) x pt) is no minf, I think.
			  ((and (eq lim '$minf) (integerp m))
			   (asymptotic-rewrite (polygamma-reflection m arg) x pt n))
			  ;; asymptotic formula toward inf
              ((and (eq '$inf lim) (eql m 0))
			  	;; log(arg) - sum(bern(k)/(k*arg^k),k,1,n), where bern(1)=1/2.
                ;; Maxima uses the standard bern(1)=-1/2, not bern(1) as required
				;; by this expansion, so we'll peel off the first term of the sum.
                ;;;;(setq arg (resimplify ($ratdisrep ($taylor arg x (ridofab pt) n))))
			    (setq k 2)
				(setq s (div 1 (mul 2 arg)))
				(while (<= k (max n 2))
					(setq ds (div ($bern k) (mul k (ftake 'mexpt arg k))))
					(incf k)
				    (setq s (add s ds)))
				(sub (ftake '%log arg) s))
				;(resimplify ($ratdisrep ($taylor (sub (ftake '%log arg) s) x pt n))))

			  (t (subfunmake '$psi (list m) (list arg)))))) 
(setf (gethash '$psi *asymptotic-rewrite-hash*) 'psi-asymptotic-rewrite)

;; See http://dlmf.nist.gov/7.11.E2. Missing the z --> -inf case.
;; Running the testsuite, this causes an asksign 
(def-asymptotic-rewrite-handler %erfc (z x pt n)
	(setq z (car z))
	(let ((s 0) (ds (div 1 z)) (k 0) (zz (mul 2 z z))
	      (lim (limit z x pt 'think)))
	  (cond ((eq '$inf lim)
			  (while (<= k n)
				 (setq s (add s ds))
				 (setq ds (div (mul ds -1 (add 1 (* 2 k))) zz))
				 (setq k (+ k 1)))
			  (mul (ftake 'mexpt '$%e (mul -1 z z)) s (div 1 (ftake 'mexpt '$%pi (div 1 2)))))
		    ((eq '$minf lim)
			  (while (< k n)
				 (setq s (add s ds))
				 (setq ds (div (mul ds -1 (add 1 (* 2 k))) zz))
				 (setq k (+ k 1)))
				(sub 2 (mul (ftake 'mexpt '$%e (mul -1 z z)) s (div 1 (ftake 'mexpt '$%pi (div 1 2)))))) 
		  (t (ftake '%erfc z)))))		

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-rewrite-hash*.

(def-asymptotic-rewrite-handler %erf (z x pt n)
	(let ((lim (limit (car z) x pt 'think))
	      (fn (gethash '%erfc *asymptotic-rewrite-hash*)))

	(cond ((and fn (or (eq lim '$inf) (eq lim '$minf)))
	       (sub 1 (funcall fn (list (car z)) x pt n)))
		  (t (fapply '%erf z)))))

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i
(def-asymptotic-rewrite-handler %gamma_incomplete (e x pt n)
	(let* ((aaa (first e)) (z (second e)) (xxx (limit-at z x pt)))
	    (setq n (max 1 n))
		(cond 
          ;; Case 1: Asymptotic expansion when z -> +/- inf and aaa is free of x
          ;; For the series, see http://dlmf.nist.gov/8.11.i
		  ((and (or (eq '$inf xxx)) (freeof x aaa)) ;;not sure about minf & infinity?
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

;; See http://dlmf.nist.gov/10.17.E3. We could also do the large order case?
(def-asymptotic-rewrite-handler %bessel_j (e x pt n)
	(let ((v (car e)) (z (cadr e)) (ω) (k 0) (a) (b) (sc 0) (cc 0))
	    (cond ((eq '$inf (limit-at z x pt))
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

;; See http://dlmf.nist.gov/10.40.E2. We could also do the large order case?
(def-asymptotic-rewrite-handler bessel_k (e x pt n)
	(let ((v (car e)) (z (cadr e)) (k 0) (a) (b) (cc 0))
	    (cond ((eq '$inf (limit-at z x pt))
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
		   (ftake 'mexpt '$%e (mul -1 z)) ;exp(-z)
		   cc)))
		(t (ftake '%bessel_k v x)))))   

; Redefine the function stirling0. The function stirling0 does more than its
;; name implies, so we will effectively rename it to asymptotic-rewrite.
(defun stirling0 (e)
  (let (($numer nil) ($float nil) (*asymptotic-max-order* 64))
   (asymptotic-rewrite e var val 0)))


(def-asymptotic-rewrite-handler %zeta (e x pt n)
  (let* ((s (car e)) (lim (let ((preserve-direction t)) (limit s x pt 'think))))
    (cond
      ;; Re(s) → +∞ : ζ(s) ≈ 1 + 2^{-s} + ... + nn^{-s}, where  nn = max(n,2)
      ((or (eq lim '$inf) (and (eq lim '$infinity) (eq (mgrp ($realpart s) 0) t))) ;not sure about the infinity case
       (let ((k 2)
             (sum 1)
             (term)
			 (nn (max n 2)))
         (while (<= k nn)
           (setq term (div 1 (ftake 'mexpt k s)))
           (setq sum (add sum term))
           (setq k (+ k 1)))
         sum))

        ;;  s → -∞  (real axis)   
        ;;  This branch uses the Riemann zeta functional equation:
        ;;      ζ(s) = 2^s · π^(s−1) · sin(π s / 2) · Γ(1−s) · ζ(1−s)

      ((eq lim '$minf)
       (let* ((one-minus-s (sub 1 s))
              (z1 (ftake '%zeta one-minus-s))
              (g1 (ftake '%gamma one-minus-s)))
         (mul
          (ftake 'mexpt 2 s)
          (ftake 'mexpt '$%pi (add s -1))
          (ftake '%sin (mul '$%pi (div s 2)))
          g1
          z1)))

      ;; s → 1 : first n Laurent terms with Stieltjes constants; the Stieltjes constants 
	  ;; do not have a simple representation.
      ((eql lim 1)
       (let* ((tau (sub s 1))
              (k 0)
              (sum (div 1 tau))
              (term))
         (while (< k n)
           (setq term
                 (mul
                  (div (mul (expt -1 k)
                            (ftake '%stieltjes k))
                       (ftake 'mfactorial k))
                  (ftake 'mexpt tau k)))
           (setq sum (add sum term))
           (setq k (+ k 1)))
         sum))

      (t (ftake '%zeta s)))))

#|

No unexpected errors found out of 14,876 tests.
Tests that were expected to fail but passed:
  C:/Users/barto/maxima-code-pure/maxima-code/tests/rtest_limit_gruntz.mac problems:
    (25 28 39 86)
Evaluation took:
  57.277 seconds of real time
  57.078125 seconds of total run time (51.953125 user, 5.125000 system)
  [ Real times consist of 2.491 seconds GC time, and 54.786 seconds non-GC time. ]
  [ Run times consist of 2.437 seconds GC time, and 54.642 seconds non-GC time. ]
  99.65% CPU
  11,141 forms interpreted
  18,279 lambdas converted
  114,336,471,059 processor cycles
  32,098,174,256 bytes consed

  

 (unless (fboundp 'old-merror)
  (setf (symbol-function 'old-merror)
        (symbol-function 'merror)))

(defmvar $print_error_messages t)
(defun merror (fmt &rest args)
  (if $print_error_messages
      (apply old-merror (cons fmt args))
      nil))
 |#
	