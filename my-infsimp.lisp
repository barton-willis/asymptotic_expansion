(in-package :maxima)

;; Return true iff e is an symbol & and extended real. The seven extended reals 
;; are minf, zerob, zeroa, ind, inf, infinity, and und. 
(defun extended-real-p (e)
  (member e (list '$minf '$zerob '$zeroa '$ind '$inf '$infinity '$und)))

;; We use a hashtable to represent the addition table of the extended real numbers.
;; Arguably the hashtable isn't the most compact way to to this, but this scheme 
;; makes it easy to extend and modify. 

;; Since limit ((x,y)-> (0+, 0-) (x+y) = 0, we use 0+ + 0- = 0.
;; Similarly for all other cases involving the limit points 
;; zerob & zeroa, we conclude that for addition zeroa and zerob
;; should be treated the same as zero. 
(defvar *extended-real-add-table* (make-hash-table :test #'equal))

(mapcar #'(lambda (a) (setf (gethash (list (first a) (second a)) *extended-real-add-table*) (third a)))
   (list (list '$minf '$minf '$minf)
         (list '$minf '$zerob '$minf)
         (list '$minf '$zeroa '$minf)
         (list '$minf '$inf '$und)
         (list '$minf '$infinity '$und)
         (list '$minf '$und '$und)
         (list '$minf '$ind '$minf)
         
         (list '$inf '$inf '$inf)
         (list '$inf '$zerob '$inf)
         (list '$inf '$zeroa '$inf)
         (list '$inf '$infinity '$und)
         (list '$inf '$und '$und)
         (list '$inf '$ind '$inf)

         (list '$infinity '$infinity '$und)
         (list '$infinity '$zerob '$infinity)
         (list '$infinity '$zeroa '$infinity)
         (list '$infinity '$und '$und)
         (list '$infinity '$ind '$infinity)

         (list '$ind '$ind '$ind)
         (list '$ind '$zerob '$ind)
         (list '$ind '$zeroa '$ind)
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

         (list '$zerob '$zerob '$zeroa)
         (list '$zerob '$zeroa '$zerob)
         (list '$zeroa '$zeroa '$zeroa)
         
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
  (let (($simp t)) (setq e ($expand e 0 0)))
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
        ((and (eq a '$ind) (integerp b) (> 0 b)) ;ind^positive integer = $ind
          '$ind)
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
       ; ((or (eq '%sum (caar e)) (eq '$sum (caar e))
       ;      (eq '%product (caar e)) (eq '$product (caar e))
      ;   (eq '$realpart (caar e)) (eq '%realpart (caar e))
      ;   (eq '$imagpart (caar e)) (eq '%imagpart (caar e)))
         
       ;  e)
        (fn (funcall fn (cdr e)))
        ;; not sure about this--subscripted functions?
      (t (simplifya (cons (list (caar e)) (mapcar #'infsimp (cdr e))) t)))))

(defun simpinf (e)
   (my-infsimp e))