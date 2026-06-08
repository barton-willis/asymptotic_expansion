;;; Maxima code for finding asymptotic expansions of various functions, including 
;;; bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, 
;;; polylogarithm, and polygamma functions. 

;;; The purpose of this code is for computing limits. Specifically
;;; limit(e,x,pt) = limit(asymptotic-rewrite(e,x,pt),x,pt) is supposed to be
;;; an identity. Possibly asymptotic-rewrite could be promoted to a user level 
;;; function, but for now it isn't intended to be a user level function.

;;; Copyright (C) 2022, 2023, 2026 Barton Willis

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
(declare-top (special *preserve-direction* *large-positive-number* var val lhp?))

(defun limit-at (arg x pt)
"Normalize directional limit points and call $limit. PT may be an ordinary limit point, $zerob, or $zeroa." 
	(cond ((eq pt '$zerob) ($limit arg x 0 '$minus))
		  ((eq pt '$zeroa) ($limit arg x 0 '$plus))
		  (t ($limit arg x pt))))

(defmvar *asymptotic-max-order* 16)

;; We provide three summation helpers, each serving a different purpose:
;;
;;   (1) sum-by-function: Computes f(0) + f(1) + ... + f(n-1).
;;         Useful when the natural summation index begins at 0. 
;;
;;   (2) sum-by-function-range: Computes f(k0) + f(k0+1) + ... + f(k1).
;;         Useful when the summation index has a natural lower bound
;;         different from 0. Avoids manual index shifting.
;;
;;   (3) sum-by-quotient:  Computes a(0) + a(1) + ... + a(n-1) when consecutive terms
;;         satisfy a(k) = a(k-1) * q(k).  Useful when the quotient q(k) has a simple form.

;; Method (1) could be eliminated and replaced by Method (2), but Method (1) is slightly
;; more efficient than is Method (2).

;; For an empty sum, all three of these summation helpers return 0.
  
;; Utility function for finding sums when the quotient of consecutive terms has a simple form. 
(defun sum-by-quotient (a0 f n)
  "Return a(0) + ... + a(n-1), where a(k) = a(k-1) * f(k)."
   (let ((sum 0) (k 0) (ds a0))
     (while (< k n)
        (setq sum (add sum ds))
        (incf k)
        (setq ds (mul ds (funcall f k))))
    sum))

;; Utility function for computing a simple finite sum.
;; Returns f(0) + f(1) + ... + f(n-1).
(defun sum-by-function (f n)
  "Return sum(f(k), k, 0, n-1)."
  (let ((sum 0))
    (dotimes (k n sum)
      (setq sum (add sum (funcall f k))))))

;; Sum f(k) for k = k0 .. k1 inclusive.
(defun sum-by-function-range (f k0 k1)
  (let ((sum 0)
        (k k0))
    (while (<= k k1)
      (setq sum (add sum (funcall f k)))
      (setq k (1+ k)))
    sum))

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

;; The function asymptotic_rewrite is only for testing, it is not intended to be a user level function.
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

(defparameter *used-ops*
  (make-hash-table :test #'eq)
  "Hashtable mapping missing operator symbols to occurrence counts.")

  (defmfun $used ()
  "Print missing operator counts sorted by descending frequency."
  (let (accum)
    ;; Collect entries
    (maphash (lambda (op count)
               (push (cons op count) accum))
             *used-ops*)

    ;; Sort by count descending
    (setf accum (sort accum #'> :key #'cdr))

    ;; Print results
    (format t "~%Used operator summary:~%")
    (dolist (entry accum)
      (format t "  ~A : ~D~%" (car entry) (cdr entry)))))

    ;; Return the sorted list as a value
    ;(fapply 'mlist accum)))

(defun asymptotic-rewrite (e x pt n)
  "Recursively rewrite an expression using asymptotic expansions. Dispatch is via a hashtable; all 
   handlers except mplus receive arguments already rewritten at order n."

  (cond
    ;; Mapatoms are unchanged
    (($mapatom e)
     e)

    ;; Special case: mplus handler receives original arguments
    ((mplusp e)
     (asymptotic-rewrite-mplus (cdr e) x pt n))

    ;; Operators we do NOT rewrite at all
    (t
     (let* ((op (caar e)))
       ;; Skip rewriting for these operators
       (when (or (member op '(%sum %product %derivative %integrate))
                 (member op '(mequal mlessp mleqp mnotequal mgreaterp mgeqp $notequal $equal)))
         (return-from asymptotic-rewrite e))

       ;; General case: dispatch to handler
       (multiple-value-bind (fn handler-args)
           (asymptotic-rewrite-dispatch e)

         ;; Track missing handlers
		 (when fn
          (incf (gethash fn *used-ops* 0)))

         ;; Rewrite arguments
         (let ((rew-args (mapcar (lambda (s) (asymptotic-rewrite s x pt n)) handler-args)))
           ;; Handler exists → call it
           (if fn
               (apply fn (list rew-args x pt n))
               ;; No handler → rebuild expression with rewritten args
               (fapply op rew-args))))))))

;; For a sum, map asymptotic-rewrite onto each summand and sum the result.
;; When the sum vanishes at order n, restart the rewrite from the *original*
;; summands at order n+1. When n reaches *asymptotic-max-order*, give up and
;; return the sum of the members of e.
;;
;; Arguments:
;;   e  – a CL list of the summand expressions
;;   x  – limit variable
;;   pt – limit point
;;   n  – truncation order
(defun asymptotic-rewrite-mplus (e x pt n)
  (let ((ans (fapply 'mplus (mapcar #'(lambda (s) (asymptotic-rewrite s x pt n)) e))))
    ;; Attempt to detect cancellation at order n. First try a cheap test ($expand ans 1 0); second,
    ;; when $expand fails to detect cancellation, test using sratsimp.
    (cond ((or (zerop1 ($expand ans 1 0))
               (zerop1 (sratsimp ans)))
           ;; If cancellation occurs and we have not exceeded the max order,
           ;; restart from the *original* summands at order n+1.
           (if (< n *asymptotic-max-order*)
               (asymptotic-rewrite (fapply 'mplus e) x pt (1+ n))
               ;; Max order reached: return the original sum.
               (fapply 'mplus e)))
          ;; No cancellation detected: return the rewritten sum.
          (t ans))))

(def-asymptotic-rewrite-handler %expintegral_ei (arg-list x pt n)
  (let* ((z (car arg-list))
         (lim (limit-at z x pt)))
    (cond
      ((eq '$inf lim)
       ;; (exp(z)/z) * sum(k!/z^k, k, 0, max(n,1)), see http://dlmf.nist.gov/6.12.E2
       (mul (div (ftake 'mexpt '$%e z) z)
            (sum-by-quotient 1  #'(lambda (k) (div k z)) (max n 1))))

      ((and (zerop2 lim))
       ;; %gamma + log(z) + sum(x^k/(k (k+1)), k, 1, (max(n,1))); see http://dlmf.nist.gov/6.6.E1
       (add '$%gamma
            (ftake '%log z) (sum-by-quotient z #'(lambda (k) (div (mul k z) (ftake 'mexpt (add 1 k) 2))) (max n 1))))

      ;; no known expansion, so return an %expintegral_ei noun form
      (t (ftake '%expintegral_ei z)))))

;; expinegral_e1(x) = -expintegral_ei(-z)  http://dlmf.nist.gov/6.2.E6  
(def-asymptotic-rewrite-handler %expintegral_e1 (arg-list x pt n)
  (let* ((z (car arg-list))
         ($expintrep '$expintegral_ei))
    (asymptotic-rewrite (mul -1 (ftake '%expintegral_ei (mul -1 z))) x pt n)))

;; %expintegral_e(p,z) = z^(p-1) * gamma_incomplete(1-p,z); see http://dlmf.nist.gov/8.19.E1 
(def-asymptotic-rewrite-handler %expintegral_e (e x pt n)
	(let* ((p (car e))
	       (z (cadr e))
		     ($expintrep '$gamma_incomplete)
		     (alt (mul (ftake 'mexpt z (sub p 1)) (ftake '%gamma_incomplete (sub 1 p) z))))
		   (asymptotic-rewrite alt x pt n)))

(defun stirling-asymptotic-expansion (arg n)
  ;; Return a truncated Poincaré-type (Stirling) asymptotic expansion for gamma(arg) as |arg| -> inf.
  ;; See http://dlmf.nist.gov/5.11.E1
  (let* (($zerobern t)  ; We want bern(even integer) = 0
         (s (sum-by-function
              #'(lambda (k)
                  (let ((kk (1+ k))) ; because sum-by-function uses k = 0..n-1
                    (div ($bern (* 2 kk))
                         (mul (* 2 kk)
                              (1- (* 2 kk))
                              (ftake 'mexpt arg (1- (* 2 kk)))))))
              (- n 1))))
    (mul (ftake 'mexpt '$%e s)
         (ftake 'mexpt (mul 2 '$%pi) (div 1 2))
         (ftake 'mexpt arg (add arg (div -1 2)))
         (ftake 'mexpt '$%e (mul -1 arg)))))

(defun gamma-reflection (z)
  ;; Apply Euler's reflection formula:  gamma(z) = pi / (sin(pi*z) * gamma(1 - z))
  ;; see http://dlmf.nist.gov/5.5.ii 
  (div '$%pi
       (mul (ftake '%sin (mul '$%pi z)) (ftake '%gamma (sub 1 z)))))
      
;; Return a truncated Poincaré-Type expansion (Stirling approximation) 
;; for gamma(e). Reference: http://dlmf.nist.gov/5.11.E1. 
(defvar *yep* 0)
(def-asymptotic-rewrite-handler %gamma (e x pt n)
  ;; negative infinity via reflection, large positive via Stirling, small via Taylor, else noun
	(let* ((arg (car e))
		     (lim (limit-at arg x pt)))
	    (cond 
        ((eq '$minf lim)
          (incf *yep* 1)
          (asymptotic-rewrite (gamma-reflection arg) x pt n))
      
        ((or (eq '$inf lim) (and (eq '$infinity lim) (off-negative-real-axisp arg))) 
          (stirling-asymptotic-expansion arg n))

        ((or (eq lim '$zeroa) (zerop2 lim))
           (let ((g (ftake '%gamma arg)))
              (resimplify ($ratdisrep (tlimit-taylor g x (ridofab pt) n)))))

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
	(let* (($zerobern t) (m (car e))
	       (arg (resimplify (cadr e)))
		     (tay-arg (tlimit-taylor arg x (ridofab pt) n))
         (lim (limit arg x pt 'think)))
        (if tay-arg
			(setq arg tay-arg)
			(return-from psi-asymptotic-rewrite  (subfunmake '$psi (list m) (list arg)))) 
		(cond ((and (eq '$inf lim) (integerp m) (>= m 1))
            (let ((s (sum-by-function 
                    #'(lambda (k) 
                         (mul (div (ftake 'mfactorial (add k m -1))
				                       (ftake 'mfactorial k)) 
				                  (div ($bern k) (ftake 'mexpt arg (add k m))))) n)))
		        (mul (ftake 'mexpt -1 (add m 1)) s)))

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
        (let* ((maxk (max n 2))
               (s0 (div 1 (mul 2 arg)))
                (summand  (lambda (k) (div ($bern k) (mul k (ftake 'mexpt arg k)))))
                (s (add s0 (sum-by-function-range summand 2 maxk))))
				(sub (ftake '%log arg) s)))

			  (t (subfunmake '$psi (list m) (list arg)))))) 
(setf (gethash '$psi *asymptotic-rewrite-hash*) 'psi-asymptotic-rewrite)

;; See http://dlmf.nist.gov/7.11.E2.  
(defun erfc-asymptotic-positive (z n)
  (let* ((a0 (div 1 z))
         (f  #'(lambda (k)  (div (mul -1 (add 1 (* 2 k))) (ftake 'mexpt z 2))))
         (s  (sum-by-quotient a0 f n)))

    (mul (ftake 'mexpt '$%e (mul -1 (ftake 'mexpt z 2)))
         s
         (div 1 (ftake 'mexpt '$%pi (div 1 2))))))

(def-asymptotic-rewrite-handler %erfc (arg-list x pt n)
  (let* ((z (car arg-list))
         ($radexpand nil)
         (lim (limit-at z x pt)))

    (cond
      ;; z → +∞
      ((eq '$inf lim)
       (erfc-asymptotic-positive z n))

      ;; z → −∞
      ((eq '$minf lim)
       ;; erfc(z) = 2 − erfc(−z)
       (sub 2 (erfc-asymptotic-positive (neg z) n)))

      ;; fallback
      (t (ftake '%erfc z)))))

;; For the series, see http://dlmf.nist.gov/8.4.
;; This sum doesn't fit into the sum-by-quotient pattern all that well, so we'll use an explicit formula for
;; the summand.
(defun gamma-incomplete-series-at-zero (p z n)
    (setq n (max n 1))
    (let ((sum (sum-by-function #'(lambda (k)  (if (eql (add k p) 0)
                                                       0
                                                      (div (ftake 'mexpt (neg z) k) (mul (ftake 'mfactorial k) (add k p))))) (max n 1))))
					(sub (mul
					       (div (ftake 'mexpt -1 (neg p)) (ftake 'mfactorial (neg p)))
					       (sub 
					         (resimplify (subfunmake '$psi (list 0) (list (sub 1 p))))
						       (ftake '%log z)))
						   (mul (ftake 'mexpt z p) sum))))

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-rewrite-hash*.
(def-asymptotic-rewrite-handler %erf (z x pt n)
	(let ((lim (limit-at (car z) x pt))
	      (fn (gethash '%erfc *asymptotic-rewrite-hash*)))
	(cond ((and fn (or (eq lim '$inf) (eq lim '$minf)))
	       (sub 1 (funcall fn (list (car z)) x pt n)))
		  (t (fapply '%erf z)))))

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i
(def-asymptotic-rewrite-handler %gamma_incomplete (arg-list x pt n)
	(let* ((p (first arg-list))
         (z (second arg-list)) 
         (lim (limit-at (ftake 'mabs z) x pt))
	       ($radexpand nil))

    (cond 
          ;; Case 1: Asymptotic expansion when z -> +/- inf and p is free of x
          ;; For the series, see http://dlmf.nist.gov/8.11.i
		  ((and (eq '$inf lim) (freeof x p)) ;;not sure about minf & infinity?
          (mul (ftake 'mexpt z (sub p 1))
               (ftake 'mexpt '$%e (mul -1 z))
               (sum-by-quotient 1 #'(lambda (k) (div (sub p k) z)) (max n 1))))

       ;; Case 2: Asymptotic expansion when z -> 0, p integer, and p <= 0
		   ;; For the series, see http://dlmf.nist.gov/8.4.E15
		   ((and (zerop2 lim) (integerp p) (>= 0 p))
		      (gamma-incomplete-series-at-zero p z n))
	     ;; Case 3: fall back			
       (t (ftake '%gamma_incomplete p z)))))

;; See http://dlmf.nist.gov/10.17.E3. We could also do the large order case?
(def-asymptotic-rewrite-handler %bessel_j (e x pt n)
	(let* ((v (car e)) (z (cadr e)) (ω) (k 0) (a) (b) (sc 0) (cc 0) (lim (limit-at z x pt)))
	    (cond ((and (eq '$inf lim) (freeof x v))
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

	  ;; ------------------------------------------------------------
      ;; z → −∞  (J_v(-z) = e^{iπv} J_v(z))
      ;; ------------------------------------------------------------
      ((and (eq '$minf lim) (freeof x v))
       (let ((zp (neg z)))
         (mul (ftake 'mexpt '$%e (mul '$%i '$%pi v))  (asymptotic-rewrite (ftake '%bessel_j v zp) x pt n))))

		(t (ftake '%bessel_j v x)))))

;; See http://dlmf.nist.gov/10.40.E2. We could also do the large order case?
(def-asymptotic-rewrite-handler %bessel_k (e x pt n)
  (let* ((v (car e))
         (z (cadr e))
         (lim (limit-at z x pt)))
    (setq n (max n 1))
    (cond
      ;; ------------------------------------------------------------
      ;; z → +∞ asymptotic expansion
      ;; ------------------------------------------------------------
      ((and (eq '$inf lim) (freeof x v))
       (flet ((f (k)
                ;; quotient a(k)/a(k-1):
                ;; ((1/2 - v + k)(1/2 + v + k)) / (-2 (k+1) z)
                (div (mul (add k (sub (div 1 2) v))
                          (add k (add (div 1 2) v)))
                     (mul -2 (add k 1) z))))
         (let ((s (sum-by-quotient 1 #'f n)))
           (mul
            ;; sqrt(pi/(2z))
            (ftake 'mexpt (div '$%pi (mul 2 z)) (div 1 2))
            ;; exp(-z)
            (ftake 'mexpt '$%e (mul -1 z))
            ;; series sum
            s))))

	  ;; ------------------------------------------------------------
      ;; z → −∞  (analytic continuation)
      ;;
      ;; K_v(z) = e^{iπv} K_v(|z|) − iπ I_v(|z|)
      ;;
      ;; We do NOT duplicate the asymptotic series.
      ;; We simply rewrite and recurse.
      ;; ------------------------------------------------------------
      ((and (eq '$minf lim) (freeof x v))
       (let ((zp (neg z)))
         (sub
          (mul (ftake 'mexpt '$%e (mul '$%i '$%pi v))
               (asymptotic-rewrite (list '%bessel_k v zp) x pt n))
          (mul '$%i '$%pi
               (asymptotic-rewrite (list '%bessel_i v zp) x pt n)))))

      ;; ------------------------------------------------------------
      ;; fallback
      ;; ------------------------------------------------------------
      (t (ftake '%bessel_k v x)))))

(def-asymptotic-rewrite-handler %bessel_i (e x pt n)
  (let* ((v (car e))
         (z (cadr e))
         (lim (limit-at z x pt)))
    (setq n (max n 1))
    (cond
      ;; ------------------------------------------------------------
      ;; z → +∞ asymptotic expansion
      ;; ------------------------------------------------------------
      ((eq '$inf lim)
       (flet ((f (k)
                ;; quotient a(k)/a(k-1):
                ;; ((1/2 - v + k)(1/2 + v + k)) / (2 (k+1) z)
                (div (mul (add k (sub (div 1 2) v))
                          (add k (add (div 1 2) v)))
                     (mul 2 (add k 1) z))))
         (let ((s (sum-by-quotient 1 #'f n)))
           (mul
            ;; exp(z)
            (ftake 'mexpt '$%e z)
            ;; 1/sqrt(2πz)
            (div 1 (ftake 'mexpt (mul 2 '$%pi z) (div 1 2)))
            s))))

      ;; ------------------------------------------------------------
      ;; z → −∞  (analytic continuation)
      ;;
      ;; I_v(-z) = e^{iπv} I_v(z)
      ;;
      ;; No K_v term appears.
      ;; ------------------------------------------------------------
      ((eq '$minf lim)
       (let ((zp (neg z)))
         (mul (ftake 'mexpt '$%e (mul '$%i '$%pi v))
              (asymptotic-rewrite (list '%bessel_i v zp) x pt n))))

      ;; ------------------------------------------------------------
      ;; fallback
      ;; ------------------------------------------------------------
      (t (ftake '%bessel_i v x)))))

(defun asymptotic-rewrite-top-level (e x pt n)
   (let* ((*asymptotic-max-order* 64))
          (cond ((zerop2 e) e)
                (t
                  (let ((ans (asymptotic-rewrite e x pt n)))
                     (if (and (< n *asymptotic-max-order*) (zerop2 ($expand ans)))
                         (asymptotic-rewrite-top-level e x pt (+ n 1))
                         ans))))))

; Redefine the function stirling0. The function stirling0 does more than its
;; name implies, so we will effectively rename it to asymptotic-rewrite-top-level.
(defun stirling0 (e)
  (asymptotic-rewrite-top-level e var val 1))

(def-asymptotic-rewrite-handler %zeta (e x pt n)
  ;; Asymptotic regimes for zeta(s):
  ;;   (1) s -> +inf : Dirichlet series truncation
  ;;   (2) s -> -inf : functional equation 
  ;;   (3) s -> 1    : Laurent expansion with Stieltjes constants 
  ;;   (4) otherwise : return noun %zeta(s)
  (let* ((s (car e))
         (lim (limit-at s x pt)))

    (cond
      ;; ------------------------------------------------------------
      ;; 1. Re(s) -> +inf
      ;;    Use the first nn = max(n,2) terms of the Dirichlet series:
      ;;      zeta(s) ~ 1 + 2^(-s) + 3^(-s) + ... + nn^(-s)
      ;;    Reference: DLMF 25.2.5
      ;; ------------------------------------------------------------
      ((or (eq lim '$inf)
           (and (eq lim '$infinity)
                (eq (mgrp ($realpart s) 0) t)))
       (let* ((nn (max n 2)))
         (add 1
              (sum-by-function
               #'(lambda (k)
                   ;; k runs 0..nn-1, but Dirichlet sum starts at 2
                   (let ((kk (+ k 2)))
                     (div 1 (ftake 'mexpt kk s))))
               (- nn 1)))))

      ;; ------------------------------------------------------------
      ;; 2. s -> -inf (real axis)
      ;;    Use the functional equation:
      ;;      zeta(s) = 2^s * pi^(s-1) * sin(pi*s/2) * gamma(1-s) * zeta(1-s)
      ;;    Reference: http://dlmf.nist.gov/25.4.E1
      ;; ------------------------------------------------------------
      ((and (eq lim '$minf) (off-negative-real-axisp s))
       (let* ((one-minus-s (sub 1 s)))
         (asymptotic-rewrite 
             (mul
                (ftake 'mexpt 2 s)
                (ftake 'mexpt '$%pi (add s -1))
                (ftake '%sin (mul '$%pi (div s 2)))
                (ftake '%gamma one-minus-s)
                (ftake '%zeta one-minus-s)) x pt n)))

      ;; ------------------------------------------------------------
      ;; 3. s -> 1
      ;;    Laurent expansion:
      ;;      zeta(s) = 1/(s-1) + sum_{k>=0} (-1)^k * gamma_k * (s-1)^k / k!
      ;;    where gamma_k are Stieltjes constants.
      ;;    Reference: http://dlmf.nist.gov/25.2.E4
      ;; ------------------------------------------------------------
      ((eql lim 1)
       (let* ((tau (sub s 1)))
         (add (div 1 tau)
              (sum-by-function
               #'(lambda (k)
                   (mul
                    (div (mul (expt -1 k)
                              (ftake '%stieltjes k))
                         (ftake 'mfactorial k))
                    (ftake 'mexpt tau k)))
               n))))

      ;; ------------------------------------------------------------
      ;; 4. No asymptotic rule applies: return noun %zeta(s)
      ;; ------------------------------------------------------------
      (t (ftake '%zeta s)))))


;; Airy–Bessel identities (DLMF 9.6.1–9.6.2):
;;   Ai(z) = (1/3)*sqrt(z) * [ J_{-1/3}( (2/3) z^(3/2) ) - J_{ 1/3}( (2/3) z^(3/2) ) ]
;;   Bi(z) = sqrt(z/3)     * [ J_{-1/3}( (2/3) z^(3/2) ) + J_{ 1/3}( (2/3) z^(3/2) ) ]
;;
;; We rewrite Ai and Bi into Bessel J and delegate all asymptotics
;; to the existing %bessel_j handler.

(def-asymptotic-rewrite-handler %airy_ai (e x pt n)
  (let* ((z (car e))
         (zz (mul (div 2 3) (ftake 'mexpt z (div 3 2))))
         (pref (mul (div 1 3) (ftake 'mexpt z (div 1 2))))
         (jneg (ftake '%bessel_j (div -1 3) zz))
         (jpos (ftake '%bessel_j (div  1 3) zz))
         (expr (mul pref (sub jneg jpos))))
    (asymptotic-rewrite expr x pt n)))

(def-asymptotic-rewrite-handler %airy_bi (e x pt n)
  (let* ((z (car e))
         (zz (mul (div 2 3) (ftake 'mexpt z (div 3 2))))
         (pref (ftake 'mexpt (div z 3) (div 1 2)))
         (jneg (ftake '%bessel_j (div -1 3) zz))
         (jpos (ftake '%bessel_j (div  1 3) zz))
         (expr (mul pref (add jneg jpos))))
    (asymptotic-rewrite expr x pt n)))

#|
Error(s) found:
  rtest_limit.mac problem:  (278)
  rtest_limit_gruntz.mac problem:   (84)
  rtest_stats.mac problem:  (10)
Tests that were expected to fail but passed:
  rtest_limit_gruntz.mac problems:  (25 28 39 86)
3 tests failed out of 19,963 total tests.
Evaluation took:
  430.647 seconds of real time
  424.765625 seconds of total run time (387.453125 user, 37.312500 system)
  [ Real times consist of 18.055 seconds GC time, and 412.592 seconds non-GC time. ]
  [ Run times consist of 17.500 seconds GC time, and 407.266 seconds non-GC time. ]
  98.63% CPU
  372,463 forms interpreted
  695,484 lambdas converted
  859,657,016,057 processor cycles
  99,099,983,648 bytes consed

(%o0)                                done
(%i1) used();

Used operator summary:
  %GAMMA-ASYMPTOTIC : 473
  POLYLOGARITHM-ASYMPTOTIC-REWRITE : 195
  %GAMMA_INCOMPLETE-ASYMPTOTIC : 65
  PSI-ASYMPTOTIC-REWRITE : 50
  %ERF-ASYMPTOTIC : 32
  %EXPINTEGRAL_EI-ASYMPTOTIC : 23
  %ZETA-ASYMPTOTIC : 13
  %BESSEL_J-ASYMPTOTIC : 2
  %BESSEL_K-ASYMPTOTIC : 1
(%o1)                                false

 |#

  ;;; patches & changes for limit.lisp

(defun limfact (n d)
  (let ((lim (toplevel-$limit (asymptotic-rewrite (div n d) var val 0) var val)))
    (if (successful-limit-result-p lim)
	    lim
		  (throw 'limit nil))))

;;; Limit(log(XXX), var, 0, val), where val is either zerob (limit from below)
;;; or zeroa (limit from above).
(defun simplimln (expr var val)
  (let ((arglim (let ((*preserve-direction* t)) (limit (cadr expr) var val 'think))) (dir))
    ;; When arglim is 0, try using behavior to determine if the limit is zerob or zeroa.
    (when (eql arglim 0)
		(setq dir (behavior expr var val))
		(cond ((eql dir -1) (setq arglim '$zerob))
		      ((eql dir 1) (setq arglim '$zeroa))))
    (cond 

	  ((not (successful-limit-result-p arglim)) (throw 'limit nil))
	  ((eq arglim '$inf) '$inf)     ;log(inf) = inf

      ;;log(minf,infinity,zerob) = infinity
	  ((member arglim '($minf $infinity $zerob))
	   '$infinity)

	  ((eq arglim '$zeroa) '$minf)  ;log(zeroa) = minf

	  ;; Special case of arglim = 0
	  ((eql arglim 0) '$infinity)
	
      ;; If expr doesn't vanish, log(ind) = ind; otherwise log(ind) = und.
	  ((eq arglim '$ind)
	      (if (eq t (mnqp (cadr expr) 0)) '$ind '$und))

	  ;; This case should be caught by simplimit, but in case simplimln is called
	  ;; from outside simplimit, we'll leave this case here for now 
	  ((eq arglim '$und) 
	    (throw 'limit nil))

      ;; log(1^(-)) = zerob, log(1^(+)) = zeroa & log(1)=0
	  ((eql (ridofab arglim) 1)
	      ;; it can happen that arglim is 1 + zeroa, for example. For such cases,
		  ;; we'll apply maybe-asksign; when that doesn't yield a sign, we'll use
		  ;; dispatch behavior.
		  (let ((sgn (maybe-asksign (sub arglim 1))))
		   (cond ((eq sgn '$neg) '$zerob)
		         ((eq sgn '$pos) '$zeroa)
				 (t
                   (setq dir (behavior (cadr expr) var val))
		           (cond ((eql dir -1) '$zerob)
		                 ((eql dir 1) '$zeroa)
			             (t 0))))))

	    (t
	       (let* ((z (trisplit arglim)) (xx (car z))  (yy (cdr z)) (sgn))
           ;; When yy vanishes, find the sign of xx. But when the sign is 'pnz', 
		   ;; use asksign. We could use 'meqp' or 'askequal' to  test for a vanishing yy,
		   ;; but for now, we'll test for a syntactic zero
			(when (eql 0 yy)
				(setq sgn (maybe-asksign xx))
				(when (eq sgn '$pnz)
		   	      (setq sgn (let ((*getsignl-asksign-ok* t)) (maybe-asksign xx)))))

	        (cond 
  		  	  ((and (eql 0 yy) (eq sgn '$neg)) ; arglim on the negative real axis
			    ;; For arglim on the negative real axis, we need to examine the imaginary
		  	    ;; part of 'expr' to see if the imaginary part of 'expr' vanishes, or if it
			    ;; approaches zero from above or below.
			   (let ((yy (cdr (trisplit (cadr expr)))))
					 (setq dir (if (eq t (meqp yy 0)) 1 (behavior yy var val)))
					 (if (eql dir 0) 
					     (throw 'limit t)
	                     (add (ftake '%log (mul -1 arglim)) (mul dir '$%i '$%pi)))))
			  ((and (eql 0 yy) (eq sgn '$zero)) '$infinity)
			  (t  (ftake '%log arglim))))))))
(setf (get '%log 'simplim%function) 'simplimln)
(setf (get '%plog 'simplim%function) 'simplimln)

(defun simplim%gamma (expr var val)
  (let* ((*preserve-direction* t) 
         (z (cadr expr))   
         (lim (limit z var val 'think)))
    ;; When lim is explicitly 0, maybe we should do more work to attempt to determine if the limit
    ;; should really be zerob or zeroa.
    (cond ((eq lim '$zeroa) '$inf)
          ((eq lim '$zerob) '$minf)
          ((eql lim 0) '$infinity) 
          ((eq lim '$minf) '$und)
          ((eq lim '$inf) '$inf)
          ((eq lim '$und) (throw 'limit nil))
          ((eq lim '$infinity) '$infinity)
          ((eq lim '$ind)
             (if (eq t (mgrp z 0))
                  '$ind 
                  '$und))

          ((and (eq '$yes ($askinteger lim)) 
                (or (member ($asksign lim) '($neg $zero)))) ;; lim <= 0

              (let* ((g (limit (sub z lim) var val 'think))
                     (sgn (if (eq '$yes (ask-integer lim '$even))
                                    1
                                    -1)))
                          (cond ((eq g '$zerob) (infsimp (mul sgn '$minf)))
                                ((eq g '$zeroa) (infsimp (mul sgn '$inf)))
                                (t (throw 'limit nil)))))

		      ((successful-limit-result-p lim) (ftake '%gamma lim))
          (t  (throw 'limit nil)))))
(setf (get '%gamma 'simplim%function) 'simplim%gamma)

#| 
;; AI written
(defmacro define-renamed-with-nlexit (old-name new-name log-var)
  "Rename OLD-NAME to NEW-NAME and wrap OLD-NAME so that any non-local
exit is recorded in LOG-VAR, which must be a place suitable for PUSH."
  (let ((args (gensym "ARGS")))
    `(progn
       ;; Save the old definition under NEW-NAME
       (setf (symbol-function ',new-name)
             (symbol-function ',old-name))

       ;; Define the wrapper under OLD-NAME
       (setf (symbol-function ',old-name)
             (lambda (&rest ,args)
               (handler-case
                   (apply #',new-name ,args)

                 (condition (c)
                   (push (ftake 'mlist :function  ',old-name
                               :renamed   ',new-name
                               ;; Maxima list of args: (mlist arg1 arg2 ...)
                               :args      (cons (list 'mlist) ,args)
                               :condition c
                               :timestamp (get-universal-time))
                         ,log-var)
                   (signal c)))))

       ',old-name)))


(defvar *nonlocal-exit* nil)
(define-renamed-with-nlexit radlim  old-radlim *nonlocal-exit*)

(defmfun $nlexit ()
  (fapply 'mlist *nonlocal-exit*))


|#

(defun extra-simp (e)
  (declare (special var))
   (let ((var-present (not (freeof var e))))
   (cond ((extended-real-p e) e) ;we don't want to call sign on ind, so catch this
		 (($mapatom e) ;if e is declared zero, return 0; otherwise e
		     (if (eq '$zero ($csign e)) 0 e))
         ;; dispatch radcan on (positive integer)^Y
         ((and (mexptp e) (integerp (cadr e)) (> (cadr e) 0))
		     ($radcan (ftake 'mexpt (cadr e) (extra-simp (caddr e)))))
		 ;; log(negative number) --> log(-negative number) + %i*%pi. This is
		 ;; needed for a nice result for integrate(x^3/(exp(x)-1),x,0,inf), for
		 ;; example.
		 ((and (eq '%log (caar e)) ($numberp (cadr e)) (eq t (mgrp 0 (cadr e))))
		 	(add (ftake '%log (mul -1 (cadr e))) (mul '$%i '$%pi)))
		 ;; When e isn't freeof var and e is a sum, map extra-simp over the
		 ;; summands, add the results, and apply sin-sq-cos-sq-sub. 
		 ((and var-present (mplusp e))
		   (sin-sq-cos-sq-sub (fapply 'mplus (mapcar #'extra-simp (cdr e))) var))
         ;; Convert gamma functions to factorials. Eventually, we should convert
		 ;; factorials to gamma functions, I think (BW).
     ((and var-present (eq 'mfactorial (caar e)))
		   (ftake '%gamma (extra-simp (add (cadr e) 1))))
		 ((and nil var-present (eq '%gamma (caar e)))
		   (ftake 'mfactorial (extra-simp (sub (cadr e) 1))))
         ;; Exponentialize the hyperbolic functions. It might be nicer to not do 
		 ;; this, but without this we get an error for limit(diff(log(tan(%pi/2*tanh(x))),x),x,inf).
		 ((and var-present (member (caar e) (list '%sinh '%cosh '%tanh '%sech '%csch '%coth)))
		 	(extra-simp ($exponentialize e)))
         ;; When X depends on var, apply reciprocal function identities such as
		 ;; csc(X) --> 1/sin(X). Specifically, do this for operators '%sec, '%csc, 
		 ;; '%cot, '%jacobi_nc, '%jacobi_ns, %jacobi_cs, %jacobi_ds, and %jacobi_dc. 
		 ;; Since the hyperbolics are exponentialized, we don't do this for the 
		 ;; hyperbolics.
		 ((and var-present (member (caar e) 
		    (list '%sec '%csc '%cot '%jacobi_nc '%jacobi_ns '%jacobi_cs '%jacobi_ds '%jacobi_dc)))
		  (div 1 (fapply (get (caar e) 'recip) (mapcar #'extra-simp (cdr e)))))
		 ;; When X or Y depends on var, convert binomial(X,Y) to factorial form.
		 ;; Same for beta(x,y). Again, I think it would be better to convert to
		 ;; gamma function form.
		 ((and var-present (member (caar e) (list '%binomial '%beta)))
		  (extra-simp ($makefact e)))
         ;; When X depends on var, do acsc(X) --> asin(1/X). Do the same
		 ;; for asec, acot, acsch, asech, and acoth.
		 ((and var-present (member (caar e) '(%acsc %asec %acot %acsch %asech %acoth)))
		  (ftake (get (get (get (caar e) '$inverse) 'recip) '$inverse) 
		     (div 1 (extra-simp (cadr e)))))
         ;; When X depends on var, convert fib(X) to its power form.
		 ((and var-present (eq '$fib (caar e)))
		  (extra-simp ($fibtophi e)))	
		 ;; convert log_gamma(X) to log(gamma(X))
		((and var-present (eq '%log_gamma (caar e)))
		  (extra-simp (ftake '%log (ftake '%gamma (cadr e)))))
        ;; convert expintegral_e to an incomplete gamma expression
        ((and var-present (eq (caar e) '%expintegral_e))
		  (let* ((p (extra-simp (cadr e)))
				 (arg (extra-simp (caddr e))))
				(mul (ftake 'mexpt arg (sub p 1))
				     (ftake '%gamma_incomplete (sub 1 p) arg))))
	     (($subvarp (mop e)) ;subscripted function
		     (subfunmake 
		      (subfunname e) 
			  (mapcar #'extra-simp (subfunsubs e)) 
			  (mapcar #'extra-simp (subfunargs e))))
		 (t (fapply (caar e) (mapcar #'extra-simp (cdr e)))))))


#|

Error summary:
Error(s) found:
  rtest_limit.mac problem:  (278)
  rtest_limit_gruntz.mac problem:  (84)
  rtest_stats.mac problem:   (10)
Tests that were expected to fail but passed:
  rtest_limit_gruntz.mac problems:  (25 28 39 86)
3 tests failed out of 19,963 total tests.
Evaluation took:
  447.788 seconds of real time
  441.921875 seconds of total run time (401.890625 user, 40.031250 system)
  [ Real times consist of 17.973 seconds GC time, and 429.815 seconds non-GC time. ]
  [ Run times consist of 17.515 seconds GC time, and 424.407 seconds non-GC time. ]
  98.69% CPU
  372,463 forms interpreted
  695,484 lambdas converted
  893,873,161,016 processor cycles
  99,096,565,184 bytes consed

(%i1) used();

Used operator summary:
  %GAMMA-ASYMPTOTIC : 473
  POLYLOGARITHM-ASYMPTOTIC-REWRITE : 195
  %GAMMA_INCOMPLETE-ASYMPTOTIC : 65
  PSI-ASYMPTOTIC-REWRITE : 50
  %ERF-ASYMPTOTIC : 32
  %EXPINTEGRAL_EI-ASYMPTOTIC : 23
  %ZETA-ASYMPTOTIC : 13
  %BESSEL_J-ASYMPTOTIC : 2
  %BESSEL_K-ASYMPTOTIC : 1

 |#