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
(declare-top (special var val))


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
             #',fname)
       ',fname)))

;; Not intended to be a user level function.
(defmfun $asymptotic_expansion (e x pt n)
	(asymptotic-rewrite e x pt n))

;; For the expression e, replace various functions (gamma, polylogarithm, and ...)
;; functions with a truncated asymptotic (Poincaré) expansions. We walk through
;; the expression tree and use hashtable to find operators with a
;; specialized function for an asymptotic expansion. When we find such an
;; operator, dispatch the function from the hashtable.

;; This code is supposed to preserve limits. By this I mean
;; limit(XXX,x,pt) = limit(YYY,x,pt), where YYY is the result
;; of applying asymptotic-rewrite to XXX.

;; fff is only used to enumerate the used operators--eventually delete this stuff
(defun asymptotic-rewrite (e x pt n)
     (catch 'asymptotic-failure
	(let (($gamma_expand nil) ;not sure about these option variables
	      ($numer nil)
		  ($float nil)
		  ($%enumer nil)
		  ($taylor_logexpand t)
		  ($domain '$complex) ;extra not sure about this
		  ($m1pbranch t) ;not sure about this
	      ($radexpand nil)
	      (fn nil) (args nil))
        ;; Unify dispatching an *asymptotic-rewrite-hash* function for both 
		;; subscripted and non subscripted functions. For a subscripted
		;; function, args = (append subscripted args, regular args).
        (cond ((and (consp e) (consp (car e)) (eq 'mqapply (caar e)))
                   (setq fn (gethash (subfunname e) *asymptotic-rewrite-hash* nil))
                   (setq args (append (subfunsubs e) (subfunargs e))))
	            ((and (consp e) (consp (car e)))
			        (setq fn (gethash (caar e) *asymptotic-rewrite-hash* nil))
                    (setq args (cdr e))))

		(cond (($mapatom e) e)
			  (fn (apply fn (list args x pt n)))
	   	      (t e)))))
;; For a sum, map asymptotic-rewrite onto the summand and sum the result. When
;; the sum vanishes, increase the truncation order and try again. When the order n 
;; reaches a magic number (8), give up and return e. 

;; The first argument e is a CL list of the summand. The second argument is the 
;; limit variable, the third is the point, and the last is the truncation level.
(def-asymptotic-rewrite-handler mplus (e x pt n)
  (let ((ans (fapply 'mplus (mapcar #'(lambda (s) (asymptotic-rewrite s x pt n)) e))))
    (cond ((zerop1 ans)
           ;; Try higher-order expansion
           (if (< n *asymptotic-max-order*)
               (asymptotic-rewrite (fapply 'mplus e) x pt (1+ n))
               (throw 'asymptotic-failure nil)))
          (t ans))))

;; Return the product of the result of mapping asymptotic-rewrite over the terms 
;; in the CL list e.
(def-asymptotic-rewrite-handler mtimes (e x pt n)
	(fapply 'mtimes (mapcar #'(lambda (s) (asymptotic-rewrite s x pt n)) e)))

;; Map asymptotic-rewrite onto the arguments of mexpt.
(def-asymptotic-rewrite-handler mexpt (e x pt n)
	(ftake 'mexpt 
		    (asymptotic-rewrite (car e) x pt n)
			(asymptotic-rewrite (cadr e) x pt n)))

;; Could we do better? Maybe  
;;   log(x^2+x) -> log(x^2) + 1/x-1/(2*x^2)+1/(3*x^3)
(def-asymptotic-rewrite-handler %log (e x pt n)
	(ftake '%log (asymptotic-rewrite (car e) x pt n)))

;; See https://dlmf.nist.gov/6.12.  Let's triple check for a Ei vs E1 flub.
(def-asymptotic-rewrite-handler %expintegral_ei (ee x pt n)
    (let* ((e (car ee)) (lim ($limit e x pt)))
	(cond ((eq '$inf lim)
		(let ((s 0) (ds) (k 0))
		  (setq e (asymptotic-rewrite e x pt n))
		  ;;(exp(-e)/ e) sum(k!/e^k,k,0,n-1). I know: this is inefficient.
		  (while (< k n)
		    (setq ds (div (ftake 'mfactorial k) (ftake 'mexpt e k)))
	 	 	(setq s (add s ds))
			(setq k (+ 1 k)))
	  	(mul s (div (ftake 'mexpt '$%e e) e))))

		;; see http://dlmf.nist.gov/6.6.E1
		((zerop2 lim)
		  (setq e (asymptotic-rewrite e x pt n))
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
	  (cond ((eq '$inf ($limit e x pt))
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
	(let ((s 0) ($zerobern t) (ds) (k 1) (xxx)) ;tricky setting for $zerobern
	    (setq e (sratsimp (car e)))
		(setq e (asymptotic-rewrite e x pt n))
		(when (eql pt 0)
			(setq pt '$zeroa))
		(setq xxx (let ((preserve-direction t)) (limit e x pt 'think)))
		;; Need to check if this is OK for infinity & minf
	    (cond ((or (eq '$inf xxx) (eq '$infinity xxx) (eq '$minf xxx))
		        (setq e (asymptotic-rewrite e x pt n))
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

(def-asymptotic-rewrite-handler mfactorial (e x pt n)
	(let ((fn (gethash '%gamma *asymptotic-rewrite-hash*)))
       (funcall fn (list (add 1 (car e))) x pt n)))

;; For the case of non integer s, see the comment in specfn.lisp about the 
;; truncation value.

;; For positive integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0003/
;; For negative integer order, see https://functions.wolfram.com/ZetaFunctionsandPolylogarithms/PolyLog/06/01/03/01/02/0001/

;; Maybe I should paste this code into li-asymptotic-expansion. But I don't think
;; that Maxima routes the minf case through li-asymptotic-expansion...
(defun polylogarithm-asymptotic-rewrite (e x pt n)
	(let (($numer nil) (s (first e)) (z (second e)) (nn) (xxx) (k 1) (acc 0))
	   (setq z (asymptotic-rewrite z x pt n))
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
(setf (gethash '$li *asymptotic-rewrite-hash*) 'polylogarithm-asymptotic-rewrite)

;; See https://en.wikipedia.org/wiki/Polygamma_function#Asymptotic_expansion 
(defun psi-asymptotic-rewrite (e x pt n)
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
(setf (gethash '$psi *asymptotic-rewrite-hash*) #'psi-asymptotic-rewrite)

;; See http://dlmf.nist.gov/7.11.E2. Missing the z --> -inf case.
;; Running the testsuite, this causes an asksign 
(def-asymptotic-rewrite-handler %erfc (z x pt n)
	(setq z (car z))
	(let ((s 0) (ds (div 1 z)) (k 0) (zz (mul 2 z z)) (xxx))
	  (setq xxx ($limit z x pt))
	  ;(setq xxx (limit z x pt 'think))
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

;; See http://dlmf.nist.gov/7.2.i. Don't directly call erfc-asymptotic, instead
;; look up the function in *asymptotic-rewrite-hash*.

(def-asymptotic-rewrite-handler erf (z x pt n)
	(let ((lim (limit (car z) x pt 'think))
	      (fn (gethash '%erfc *asymptotic-rewrite-hash*)))
	(cond ((eq lim '$inf)
	       (sub 1 (funcall fn z x pt n)))
		  (t (fapply '%erf z)))))

;; Need to include the cases: large a, fixed z, and fixed z/a cases. 
;; See http://dlmf.nist.gov/8.11.i
(def-asymptotic-rewrite-handler %gamma_incomplete (e x pt n)
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

;; See http://dlmf.nist.gov/10.17.E3. We could also do the large order case?
(def-asymptotic-rewrite-handler %bessel_j (e x pt n)
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

;; See http://dlmf.nist.gov/10.40.E2. We could also do the large order case?
(def-asymptotic-rewrite-handler bessel_k (e x pt n)
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
		   (ftake 'mexpt '$%e (mul -1 z)) ;exp(-z)
		   cc)))
		(t (ftake '%bessel_k v x)))))   

; Redefine the function stirling0. The function stirling0 does more than its
;; name implies, so we will effectively rename it to asymptotic-rewrite.

;; The identifiers var and val look too similar to me--I'm going to use x for
;; the limit variable and pt for the limit point.
(defun stirling0 (e &optional (x var) (pt val) (n 1))
  (let (($numer nil) ($float nil) (*asymptotic-max-order* (* 4 n)))
    (catch 'asymptotic-failure
      (or (asymptotic-rewrite e x pt n) e))))


