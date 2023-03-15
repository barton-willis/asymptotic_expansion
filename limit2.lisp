(in-package :maxima)	
(declare-top (special limit-assumptions var val lhcount lhp? *behavior-count-now*))

(defun limit2-old (n dn var val)
  (prog (n1 d1 lim-sign gcp sheur-ans)
     (setq n (hyperex n) dn (hyperex dn))
;;;Change to uniform limit call.
     (cond ((infinityp val)
	    (setq d1 (limit dn var val nil))
	    (setq n1 (limit n var val nil)))
	   (t (cond ((setq n1 (simplimsubst val n)) nil)
		    (t (setq n1 (limit n var val nil))))
	      (cond ((setq d1 (simplimsubst val dn)) nil)
		    (t (setq d1 (limit dn var val nil))))))
     (cond ((or (null n1) (null d1)) (return nil))
	   (t (setq n1 (sratsimp n1) d1 (sratsimp d1))))
     (cond ((or (involve n '(mfactorial)) (involve dn '(mfactorial)))
	    (let ((ans (limfact2 n dn var val)))
	      (cond (ans (return ans))))))
     (cond ((and (zerop2 n1) (zerop2 d1))
	    (cond  ((not (equal (setq gcp (gcpower n dn)) 1))
		    (return (colexpt n dn gcp)))
		   ((and (real-epsilonp val)
			 (not (free n '%log))
			 (not (free dn '%log)))
		    (return (liminv (m// n dn))))
		   ((setq n1 (try-lhospital-quit n dn nil))
		    (return n1))))
	   ((and (zerop2 n1) (not (member d1 '($ind $und) :test #'eq))) (return 0))
	   ((zerop2 d1)
	    (setq n1 (ridofab n1))
	    (return (simplimtimes `(,n1 ,(simplimexpt dn -1 d1 -1))))))
		
     (setq n1 (ridofab n1))
     (setq d1 (ridofab d1))
     (cond ((or (eq d1 '$und)
		(and (eq n1 '$und) (not (real-infinityp d1))))
	    (return '$und))
           ((eq d1 '$ind)
	    ;; At this point we have n1/$ind. Look if n1 is one of the
	    ;; infinities or zero.
	    (cond ((and (infinityp n1) (eq ($sign dn) '$pos))
		   (return n1))
		  ((and (infinityp n1) (eq ($sign dn) '$neg))
		   (return (simpinf (m* -1 n1))))
		  ((and (zerop1 n1)
			(or (eq ($sign dn) '$pos)
			    (eq ($sign dn) '$neg)))
		   (return 0))
		  (t (return '$und))))
	   ((eq n1 '$ind) (return (cond ((infinityp d1) 0)
					((equal d1 0) '$und)
					(t '$ind)))) ;SET LB
	   ((and (real-infinityp d1) (member n1 '($inf $und $minf) :test #'eq))
	    (cond ((and (not (atom dn)) (not (atom n))
			(cond ((not (equal (setq gcp (gcpower n dn)) 1))
			       (return (colexpt n dn gcp)))
			      ((and (eq '$inf val)
				    (or (involve dn '(mfactorial %gamma))
					(involve n '(mfactorial %gamma))))
			       (return (limfact n dn))))))
		  ((eq n1 d1) (setq lim-sign 1) (go cp))
		  (t (setq lim-sign -1) (go cp))))
	   ((and (infinityp d1) (infinityp n1))
	    (setq lim-sign (if (or (eq d1 '$minf) (eq n1 '$minf)) -1 1))
	    (go cp))
	   (t (return (simplimtimes `(,n1 ,(m^ d1 -1))))))
     cp   (setq n ($expand n) dn ($expand dn))
     (cond ((mplusp n)
	    (let ((new-n (m+l (maxi (cdr n)))))
	      (cond ((not (alike1 new-n n))
		     (return (limit (m// new-n dn) var val 'think))))
	      (setq n1 new-n)))
	   (t (setq n1 n)))
     (cond ((mplusp dn)
	    (let ((new-dn (m+l (maxi (cdr dn)))))
	      (cond ((not (alike1 new-dn dn))
		     (return (limit (m// n new-dn) var val 'think))))
	      (setq d1 new-dn)))
	   (t (setq d1 dn)))
     (setq sheur-ans (sheur0 n1 d1))
     (cond ((or (member sheur-ans '($inf $zeroa) :test #'eq)
		(free sheur-ans var))
	    (return (simplimtimes `(,lim-sign ,sheur-ans))))
	   ((and (alike1 sheur-ans dn)
		 (not (mplusp n))))
	   ((member (setq n1 (cond ((expfactorp n1 d1)  (expfactor n1 d1 var))
				 (t ())))
		  '($inf $zeroa) :test #'eq)
	    (return n1))
	   ((not (null (setq n1 (cond ((expfactorp n dn)  (expfactor n dn var))
				      (t ())))))
	    (return n1))
	   ((and (alike1 sheur-ans dn) (not (mplusp n))))
	   ((not (alike1 sheur-ans (m// n dn)))
	    (return (simplimit (m// ($expand (m// n sheur-ans))
				    ($expand (m// dn sheur-ans)))
			       var
			       val))))
     (cond ((and (not (and (eq val '$inf) (expp n) (expp dn)))
		 (setq n1 (try-lhospital-quit n dn nil))
		 (not (eq n1 '$und)))
	    (return n1)))
     (throw 'limit t)))

;; When limit(e,x,pt) = 0, we dispatch behavior to attempt to decide
;; if the limit is zerob, zeroa, or 0. The function behavior misses 
;; some cases that it might. At one time this code caught a few more
;; cases by dispatching taylor, but if that is a good idea, it should
;; be blended into behavior, not this code.
(defun zero-fixup (e x pt)
   (let ((*behavior-count-now* 0) (dir (behavior e x pt)))
	(cond ((eql dir -1) '$zerob)
		  ((eql dir 1) '$zeroa)
		  (t 0))))

(defvar *extended-real-divide-table* (make-hash-table :test #'equal))
(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-divide-table*) (third a)))
   (list 
      (list '$minf '$zerob '$inf)
      (list '$minf '$zeroa '$minf)
      (list '$zerob '$minf '$zeroa)
      (list '$zerob '$inf '$zerob)
	  (list '$zerob '$infinity 0)
      (list '$zeroa '$inf '$zeroa)
	  (list '$zeroa '$minf '$zerob)
      (list '$zeroa '$infinity 0)
      (list '$ind '$minf 0)
	  (list '$ind '$inf 0)
	  (list '$ind '$infinity 0)
      (list '$inf '$zerob '$minf)
      (list '$inf '$zeroa '$inf)
      (list '$infinity '$zerob '$infinity)
      (list '$infinity '$zeroa '$infinity)))

(defvar *calls* 0)
(defvar *limit2* nil)
(defvar *const* 0)
;; Running the testsuite, limit2-old is called 404 times (out of 1736 calls 
;; to limit2). Among these 404 calls, there are 17 distinct values for 
;; the ordered pair (nl dl). Some of these calls do not involve an
;; indeterminate form; for example [ind,ind],[inf,ind],[-inf,0],[und,inf],
;; [zeroa,ind],and [zerob,ind]. We should try to catch these cases before
;; sending them the old limit2

;; It's tempting to examine n & d for a common factor, but doing so can 
;; cause infinite loops. Example: gcd(x, 1/log(x)) is 1/log(x). 
(defun limit2 (n d x pt)
     (incf *calls* 1)
	(let ((dir) (nl) (dl) (var x) (val pt) (nsgn) (dsgn) (preserve-direction t))

	    ;(mtell "Top limit2  ~M ~%" (sratsimp ($minfactorial (div n d))))
        ;(setq n (stirling0 n))
		;(setq d (stirling0 d))
        (setq nl (sratsimp (limit n x pt 'think)))
        ;; Running the testsuite, this call to zero-fixup causes an asksign--for 
		;; now let's turn it off.
        ;(when (eql nl 0)
        ;    (setq nl (zero-fixup n x pt)))

	    (setq dl (limit d x pt 'think))
        (when (eql dl 0)
            (setq dl (zero-fixup d x pt)))

        (let ((*complexsign* t))
			(setq nsgn (car (errcatch ($csign nl))))
            (setq dsgn (car (errcatch ($csign dl)))))

       ; (mtell "nl = ~M ; dl = ~M ; ~%" nl dl)
		;; When we call gruntz, we need to know the direction of the limit.
        (setq dir (cond ((eq pt '$zerob) '$minus)
		                ((eq pt '$zeroa) '$plus)
						((eq pt '$inf) '$minus)
						((eq pt '$minf) '$plus)
						(t nil)))
		(cond 
              ;; When Maxima is unable to find the limit of either the
              ;; numerator or denominator (either nl or dl is nil), return nil.
			  ;; Presumably, Maxima has exhausted all other methods to find 
			  ;; the limit of n/d, so we don't call limit on n/d.
              ((or (null nl) (null dl)) nil)

			  ;; When either nl or dl is und, we don't want to give up just now--the
			  ;; limit of the quotient might exist. But we do check for the limit
			  ;; of a constant case. Does this ever catch anything?
			  ((and (freeof x d) (freeof x n) (eql t (mnqp d 0)))
			    (incf *const* 1)
			    (div n d))

              ;; When n (not nl) is zero and the limit of the denominator 
			  ;; is nonzero, return zero. Is the test (eql t (mnqp dl 0) too lenient? 
              ((and (eql 0 n) (eql t (mnqp dl 0)))
			    0)

              ;; When both nl and dl are extended reals, but the quotient nl/dl 
              ;; is determinate, look up the quotient. These cases
              ;; include ind/inf = 0 and zeroa/inf =  zeroa.
              ((gethash (list nl dl) *extended-real-divide-table* nil))

              ;; nl/1 = nl.
              ;;;((eql dl 1) nl)
             
              ;; nl/minf = 0, nl/inf = 0, and nl/infinity = 0, where
              ;; nl is ind or not an extended real.
		      ((and (or (eq dl '$minf) (eq dl '$inf) (eq dl '$infinity))
			        (or (eql nl '$ind) (not (extended-real-p nl))))
				0)

              ;; (positive real)/zeroa = inf and (negative real)/zeroa = minf)
			  ((and (eq dl '$zeroa) (not (extended-real-p nl))
			        (or (eq nsgn '$neg) (eq nsgn '$pos)))
			   (if (eq nsgn '$neg) '$minf '$inf))

               ;; complex/zeroa = infinity and complex/zerob = infinity. 
			   ;; Is this too lenient?
			   ((and (or (eq nsgn '$complex) (eq nsgn '$imaginary)) 
			         (or (eq dl '$zerob) (eq dl '$zeroa)))
			      '$infinity)
            
              ;; inf/(minus one), where ridofab(minus one) = -1. This should be
              ;; generalized.
			  ((and (eq nl '$inf) (eql -1 (ridofab dl)))
                '$minf)

              ;; (positive real)/zerob = minf and (negative real)/zerob = inf)
			  ((and (eq dl '$zerob) (not (extended-real-p nl))
			        (or (eq nsgn '$neg) (eq nsgn '$pos)))
			   (if (eq nsgn '$neg) '$inf '$minf))

              ;; zeroa/(negative real) = zerob and zeroa/(positive real) = zeroa
              ((and (eq nl '$zeroa) (not (extended-real-p dl))
                   (or (eq dsgn '$neg) (eq dsgn '$pos)))
                (if (eq dsgn '$neg) '$zerob '$zeroa))

              ;; zerob/(negative real) = zeroa and zerob/(positive real) = zerob
              ((and (eq nl '$zerob) (not (extended-real-p dl))
                   (or (eq dsgn '$neg) (eq dsgn '$pos)))
                (if (eq dsgn '$neg) '$zeroa '$zerob))

              ;; ind/nonzero = ind
              ((and (eq nl '$ind) 
                    (or (eq nsgn '$neg) (eq nsgn '$pn) (eq nsgn '$pos)))
                '$ind)

              ;; When both n & d involve the factorial--this is messed up?
			  ;; Bug for limit(gamma(1/x)-x,x,'inf). Does striling0 not 
			  ;; properly check stuff?
              ((and (involve n '(mfactorial))
                    (involve d '(mfactorial))
				    (limfact n d)))
   
              ;; Dispatch the gruntz code on n/d.
			  ((car (let (($algebraic t)) 
			     (errcatch (gruntz1 (div n d) x pt dir))))) 

			  ;; Punt to old limit2 code (renamed limit2-old)
		      ((or (extended-real-p nl) 
		           (extended-real-p dl)
				   (eql 0 (ridofab dl)))
				(push (ftake 'mlist nl dl) *limit2*)
		        (limit2-old n d x pt))
			  ;; Limit by direct substitution.
			  (t (div nl dl)))))


