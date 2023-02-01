;; Author: Barton Willis with help from Richard Fateman

#|
To simplify a sum with n terms, the standard simplus function calls
great O(n^2) times. By using sorting more effectively, this code
reduces the calls to O(n log_2(n)).

Also, this code tries to be "infinity correct" for addition. By this I
mean inf + inf --> inf, inf + number --> inf, and inf + minf --> und.
Since -1 * inf does not simplify to minf, this code doesn't simplify
inf - inf to und; consequently, this portion of the code is largely
untested. There are other problems too.  For one, this code does
f(inf) - f(inf) --> 0 (comment from Stavros Macrakis). I don't know
how far we can go with such things without making a mess. You could
argue that Maxima should do

   f(x) - f(x) --> if finitep(f(x)) then 0 else und 

instead of f(x) - f(x) --> 0.

There is a great deal more that could be done. We could tag each
infinity with a unique identifier (idea from RJF). That way we could
have x : inf, x - x --> 0 and x : inf, y : inf, x - y --> und, for
example.

In short, this code is highly experimental; you should not use it for
anything that is important. I place it in /share/contrib because
others encouraged me too; also I thought it might be useful to others
who would like to experiment with similar code. Since a great deal of
work has gone into the current simplus code, I'm not sure that a total
rewrite is the best route.

Maybe the special case dispatch part of this code makes the task of
extending simplus (to intervals, for example) easier. The basic design
of this code is due to Barton Willis.
|#

#| 

As of late May 2021, altsimp (with use_extended_real_arithmetic set to false), runs 
the testsuite + the share testsuite with nine failures; the failures are

 rtest11.mac problems (4 8)
 rtest14.mac problem: (62)
 rtest16.mac problems:  (457 459)
 rtest_expintegral.mac problems: (173 174)
 rtest_dgesv.mac problem: (5)
 rtest_to_poly_solve.mac problem: (241)

Reasons for these failures include:

* Standard Maxima simplifies 2^a+3*2^(a+1) to 7*2^a, but altsimp misses this simplification.
* Altsimp simplifies 2^(3/2)-sqrt(2)*x^2 to sqrt(2)*x^2, but standard Maxima misses this.
* Possible differences in ordering of addition of floating point numbers.

Using CCL 12.1 (64 bit) and altsimp, timings are:

took 752,166,000 microseconds (752.166000 seconds) to run.
      12,556,790 microseconds ( 12.556790 seconds, 1.67%) of which was spent in GC.
During that period, and with 4 available CPU cores,
     687,062,500 microseconds (687.062500 seconds) were spent in user mode
      38,109,375 microseconds ( 38.109375 seconds) were spent in system mode
87,194,237,408 bytes of memory allocated.

And timings for standard Maxima are:

took 689,231,000 microseconds (689.231000 seconds) to run.
      11,857,789 microseconds ( 11.857789 seconds, 1.72%) of which was spent in GC.
During that period, and with 4 available CPU cores,
     644,234,375 microseconds (644.234400 seconds) were spent in user mode
      23,062,500 microseconds ( 23.062500 seconds) were spent in system mode
 77,100,115,920 bytes of memory allocated.

 Compared to standard Maxima, altsimp runs the testsuites more slowly and uses more
 memory. Using sbcl 2.0, the results are similar, but faster and more memory.

Expected testsuite failures that are fixed:

* integrate(exp(2^(3/2)*x^2-sqrt(2)*x^2),x) is OK. This is due to the fact that with altsimp,
    exp(2^(3/2)*x^2-sqrt(2)*x^2) simplifies to %e^(sqrt(2)*x^2).

Speculation on how to speed up simplication of sums:

The altsimp algorithm uses sorting to speed up simplication of expressions with a 
large number of summands, but at least for running the testsuites, simplus is mostly 
called with just two summands. If one of the two summands is a sum, say XXX, altsimp 
re-examines the terms of XXX for common terms. That is, of course, wasteful. If the 
summands were marked in a way that indicated that pairs of terms were not common, that 
would possibly speed the code.

|#

(in-package :maxima)

(declare-top (special dosimp))
(declaim (optimize (speed 3) (safety 0)))

(define-modify-macro mincf (&optional (i 1)) addk)

;; Return true if z = 0, 0.0, or a bigfloat zero.
(defun mzerop (z)
  (and (mnump z)
       (or (and (numberp z)(= z 0))
	         (and (bigfloatp z)(= (cadr z) 0))))) ;bigfloat zeros may be diff precisions

;; Return true if x has the form integer^(rational)
(defun surd-p (x)
  (and (mexptp x) (integerp (cadr x)) ($ratnump (caddr x))))

(defun surd-convert (x)
   (cond ((or (integerp x) (mnump x))
           (cons 1 x))
         ((surd-p x) 
          ;; x = a^(p/q) = a^n * a^(p/q - n), where n = floor(p/q). 
            (let ((a (cadr x)) (p (caddr x)) (q) (n))
              (setq q ($denom p))
              (setq p ($num p))         
              (setq n (floor (/ p q)))
              (cons (take '(mexpt) a (sub (caddr x) n)) (take '(mexpt) a n))))
          (t (cons x 1))))
  
;; Convert a term (a non sum expression) to the form (e . coefficient), where
;; coefficient is a rational or floating point number. Factors of the form
;; integer^(rational) are converted by surd-convert.
(defun convert-to-coeff-form (x)  
  (let ((c 1) (xx) (qq 1))
    (cond ((mnump x) (cons 1 x))
          ((surd-p x)
            (surd-convert x))

	        ((mtimesp x) 
	          (pop x)  ;remove (car x) which is (mtimes ..)
            (while (or (mnump (car x)) (surd-p (car x)))
               (setq xx (surd-convert (car x)))
               (setq c (mul c (cdr xx)))
               (setq qq (mul qq (car xx)))
               (pop x))

            (when (not (eql qq 1))
                (push qq x))

            (when (null x)
               (push 1 x))

	          (if (null (cdr x)); if only one more item, that's it.
		              (cons (car x) c)
		              (cons (cons (get 'mtimes 'msimpind) x) c)))
          (t (cons x 1)))))

;; Previously there was a specialized function for multiplying a number times an expression. The
;; motivation was, I think, speed. But the specialized function was responsible for 22 testsuite
;; failures (May 2021) and it didn't contribute to running the testsuite any faster. So let us 
;; replace the specialized function with a call to mul. 

(defun number-times-expr (cf e)
  (mul cf e))

;; Add an expression x to a list of equalities l.
(defun add-expr-mequal (x l)
  (setq l (mapcar 'cdr l))
  (push (list x x) l)
  (setq l (list (reduce #'add (mapcar 'first l)) (reduce #'add (mapcar 'second l))))
  (simplifya (cons '(mequal) l) t))
  
(defun add-expr-mrat (x l)
  (ratf (cons '(mplus) (cons (ratf x) l))))

(defun add-expr-taylor (x l)
  ($taylor (cons '(mplus) (cons x l))))

(defun add-expr-mlist (x l)
  (setq l (if (cdr l) (reduce 'addmx l) (car l)))
  (simplifya (cons (list 'mlist) (mapcar #'(lambda (s) (add x s)) (cdr l))) t))

;; Simple demo showing how to define addition for a new object.
;; We could append simplification rules for intervals:
;;  (a) interval(a,a) --> a,
;;  (b) if p > q then interval(p,q) --> standardized empty interval?

(defun add-expr-interval (x l)
  (setq l (mapcar #'(lambda (s) `((mlist) ,@(cdr s))) l))
  (setq l (if (cdr l) (reduce #'addmx l) (car l)))
  (simplifya (cons (list '$interval) (mapcar #'(lambda (s) (add x s)) (cdr l))) t))
 
;; Add an expression x to a list of matrices l. The Maxima function mxplusc
;; calls pls. Here is a version that doesn't call pls. I'm not sure I've captured all 
;; features of mxplusc.
(defun add-expr-matrix (x l)
  (setq l (if (cdr l) (reduce #'addmx l) (car l)))
  (cond ((and $listarith ($matrixp l))
          (let ((errset nil)
		            (errcatch t)
            		($errormsg nil)
		            (*mdebug* nil))
                (setq x (errset (simplifya (cons '($matrix) (cdr (add x ($args l)))) t)))
                (if x (car x) (merror "Attempt to add noncomformable matrices"))))
        (t (list (get 'mplus 'msimpind) x l))))

;; Return a + b, where a, b in {minf, inf, ind, und, infinity}. I should
;; extend this to allow zeroa and zerob (but I'm not sure zeroa and zerob
;; are supposed to be allowed outside the limit code). We use a hashtable
;; to represent the multiplication table--this should be easy to extend
;; and modify.
(defvar *extended-real-add-table* (make-hash-table :test #'eq :size 16))

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
         (list '$infinity '$und '$und)
         (list '$infinity '$ind '$infinity)

         (list '$ind '$ind '$ind)
         (list '$ind '$und '$und)

         (list '$und '$und '$und)))

(defun add-extended-real(a b)  
  (gethash (list a b) *extended-real-add-table* (gethash (list b a) *extended-real-add-table* '$und)))

;; Add an expression x to a list of infinities. We do explicit number + extended real --> extended real, 
;; but for a general expression XXX we do XXX + extended real --> nounform. We could, of course, 
;; extend the logic of XXX + extended real. But at least XXX + extended real --> nounform isn't wrong.
(defun add-expr-infinities (x l) 
  (setq l (if l (reduce #'add-extended-real l) (car l)))
  (if (mnump x) l (list (get 'mplus 'msimpind) x l)))

;; The functions pls & plusin are parts of the standard simplus code. Let's issue
;; errors when these functions are called. Unfortunately, code in share\affine calls
;; pls directly, so the affine code will not run using altsimp.	
(defun pls (x out)
    (mtell "in pls; x = ~M,  out = ~M ~%" x out)
    (merror "Error: called pls ~%"))

(defun plusin (x fm) 
   (mtell "in plusin; x = ~M,  fm = ~M ~%" x fm)
   (merror "Error: called plusin ~%"))

;; I assumed that if a list of distinct members is sorted using great,
;; then it's still sorted after multiplying each list member by a nonzero
;; maxima number. I'm not sure this is true.

;; If l has n summands, simplus calls great O(n log_2(n)) times. All
;; other spendy functions are called O(n) times. The standard simplus
;; function calls great O(n^2) times, I think.

;; When the option variable $use_extended_real_arithmetic is true, simplus adds the extended real 
;; numbers (minf,inf,infinity, und, ind) in a mathematically logicaly way. But since simptimes and
;; simpexpt do not have an option of doing correct extended real number arithmetic, this feature of
;; simplus is limited.

(defmvar $use_extended_real_arithmetic t)

;; The binary64 value of %e.
(defvar %e-float64 (exp 1.0d0))

(defun simplus (l w z)
  (declare (ignore w))
  
  (let ((acc nil) (cf) (x) (num-sum 0) (do-over nil) (mequal-terms nil) (mrat-terms nil) 
	(inf-terms nil) (matrix-terms nil) (mlist-terms nil) (taylor-terms nil) (interval-terms nil) 
  (op) (atom-hash (make-hash-table :test #'eq :size 8)))

  (setq l (margs l))
  ;; simplfy and flatten
    (dolist (li l)
    	(setq li (simplifya li z))
     ;; When numer is true, simplifya converts %pi & %phi to their binary64 value,
     ;; but only converts %e when both numer & %enumer are true. Here we convert
     ;; %e to its binary64 value.
     (when (and $numer (atom li) (eq li '$%e)) ; $%e --> 2.718...
        (setq li  %e-float64))
    	(if (mplusp li) (setq acc (append acc (cdr li))) (push li acc)))

    (setq l acc)
    (setq acc nil)
    (dolist (li l)
      (cond ((mnump li) (mincf num-sum li))
	          ;; factor out infrequent cases.
          	((and (consp li) (consp (car li)) (member (caar li) '(mequal mrat $matrix mlist $interval)))
	                (setq op (caar li))
	                (cond ((eq op 'mequal)
		                      (push li mequal-terms))
		                    (($taylorp li)
	                  	    (push li taylor-terms))
		                    ((eq op 'mrat)
		                       (push li mrat-terms))
		                    ((eq op '$matrix)
		                       (push li matrix-terms))
		                    ((eq op '$interval)
		                       (push li interval-terms))
		                    ((eq op 'mlist)
		                      (if $listarith (push li mlist-terms) (push (convert-to-coeff-form li) acc))))) 

	            ;; Put non-infinite atoms into a hashtable; push infinite atoms into inf-terms.
	            ((atom li)
	                (if (and $use_extended_real_arithmetic (member li '($minf $inf $infinity $und $ind)))
		                     (push li inf-terms)
	                    (progn
		                      (setq cf (gethash li atom-hash))
		                      (setf (gethash li atom-hash) (if cf (1+ cf) 1)))))

	        (t (push (convert-to-coeff-form li) acc))))

     ;; push atoms in the hashtable into the accumulator acc; sort acc.
    (maphash #'(lambda (cf a) (push (cons cf a) acc)) atom-hash)
    (setq l (sort acc 'great :key 'car))
 
    ;; common term crunch: when the new coefficient is -1 or 1 (for example, 5*a - 4*a),
    ;; set the "do-over" flag to true. In this case, the sum needs to be re-simplified.
    ;; Without the do over flag, a + 5*a - 4*a --> a + a. Last I checked, the testsuite
    ;; does not test the do-over scheme.

    (setq acc nil)
    (while l
      (setq x (pop l))
      (setq cf (cdr x))
      (setq x (car x))
      (while (and l (like x (caar l)))
      	(mincf cf (cdr (pop l))))
        (if (and (or (eql cf 1) (eql cf -1)) (mplusp x)) (setq do-over t))
        (setq x (number-times-expr cf x))
        (cond ((mnump x) (mincf num-sum x))
	            ((not (mzerop x)) (push x acc))))

    ;; Do x + 0 --> x, x + 0.0 --> x, and x + 0.0b0 --> x.
    (if (not (mzerop num-sum)) (push num-sum acc))
   
    (setq acc
	  (cond (do-over (simplifya `((mplus) ,@acc) nil))
      		((null acc) num-sum)
		      ((null (cdr acc)) (car acc))
		      (t (cons '(mplus simp) acc))))
    
    ;; special case dispatch
    (when mequal-terms
	     (setq acc (add-expr-mequal acc mequal-terms)))
    (when taylor-terms
    	(setq acc (add-expr-taylor acc taylor-terms)))
    (when mrat-terms
	      (setq acc (add-expr-mrat acc mrat-terms)))
    (when mlist-terms
	      (setq acc (add-expr-mlist acc mlist-terms)))
    (when interval-terms
      	(setq acc (add-expr-interval acc interval-terms)))
    (when matrix-terms
	      (setq acc (add-expr-matrix acc matrix-terms)))
    (when inf-terms
      	(setq acc (add-expr-infinities acc inf-terms)))   
    acc))

;; The expression e must be simplified (ok)
;;   (a) 1 * x --> x,
;;   (b) 0 * x --> 0, 0.0 * x --> 0.0, 0.0b0 * x --> 0.0b0
;;   (c) cf * e --> timesk(ck,e) when e is a maxima number,
;;   (d) -1 * (a + b) --> -a - b,
;;   (e) cf * (* a b c) --> (* (* cf a) b c ...) when a is a number; otherwise (* cf a b ...)
;;   (f) (* cf e) (default)

;; alg is a list of the form ((p1 n1) (p2 n2) ...) where the number is p1^n1 * p2^n2, ...

(defun number-times-expr-fast (cf e)
  ;(mtell "cf = ~M e = ~M ~%" cf e)
  (cond ((or (mzerop cf) (mzerop e)) 0)

        ((eql cf 1) e)
        ((eql e 1) cf)
      	;;  -1 * (a + b + ... + z) --> -a + -b + ... + -z.
      	((and (eql cf -1) (mplusp e))
	       (addn (mapcar #'neg (cdr e)) t))

      	((and (mnump cf) (mnump e))
	        (timesk cf e))
	 
      	((and (mtimesp e) (mnump (second e)))
          (setq cf (mul cf (second e)))
          (cons (get 'mtimes 'msimpind) (cons cf (cddr e))))
        
        ((mtimesp e)
          (cons (get 'mtimes 'msimpind) (cons cf (cdr e))))

        (t (cons (get 'mtimes 'msimpind) (list cf e)))))
	

(defun mult-lists (p q)
  (let ((acc nil))
    (dolist (pk p acc)
      (dolist (qk q)
	(push (mul pk qk) acc)))))

;;We use a hashtable to represent the multiplication table for extended 
;; real numbers. The table is symmetric, so we only list its "upper" half.
(defvar *extended-real-mult-table* (make-hash-table :test #'eq :size 16))
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

(defun mult-extended-real (a b)
  (or (gethash (list a b) *extended-real-mult-table* nil)
	    (gethash (list b a) *extended-real-mult-table* '$und)))


;; minf, ind und, inf, infinity.

(defun mult-expr-infinities (x l) 
  (let ((sgn))
    (setq l (if l (reduce 'mult-extended-real l) (car l)))
    (if (eq l '$und) '$und
      (progn
	(setq sgn ($csign x))
	(cond ((eq sgn '$neg)
	       (cond ((eq l '$minf) '$inf)
		     ((eq l '$ind) '$ind)
		     ((eq l '$und) '$und)
		     ((eq l '$inf) '$minf)
		     ((eq l '$infinity) '$infinity)))

	      ((eq sgn '$zero)
	       (if (eq l '$ind) 0 '$und))
	      
	      ((eq sgn '$pos)
	       (cond ((eq l '$minf) '$minf)
		     ((eq l '$ind) '$ind)
		     ((eq l '$und) '$und)
		     ((eq l '$inf) '$inf)
		     ((eq l '$infinity) '$infinity)))

        ((or (eq sgn '$complex) (eq sgn '$imaginary)) 
         (cond ((eq l '$ind) '$ind) ;not sure
               ((eq l '$und) '$und)
               (t '$infinity)))

	      (t (cons '(mtimes simp) (sort (cons l (if (mtimesp x) (cdr x) (list x))) 'great))))))))
	
(defun convert-to-expon-form (a)
  (if (mexptp a) (cons (second a) (third a)) (cons a 1)))

(defun mult-common-terms (a b)
  (setq a (convert-to-expon-form a)) 
  (setq b (convert-to-expon-form b))
  (if (like (car a) (car b)) (take '(mexpt) (car a) (add (cdr a) (cdr b))) nil))

(defun mult-expr-mrat (x l)
  (ratf (cons '(mtimes) (cons x l))))

(defun mult-expr-taylor (x l)
  ($taylor (cons '(mtimes) (cons x l))))

(defun mult-expr-mequal (x l)
  (opcons 'mequal (mul x (reduce 'mul (mapcar 'second l))) (mul x (reduce 'mul (mapcar 'third l)))))

(defun mult-expr-mlist (x l)
  (mxtimesc x (if (cdr l) (reduce 'stimex l) (car l))))

(defun mult-expr-matrix (x l)
  (mxtimesc x (if (cdr l) (reduce 'stimex l) (car l))))

;; l is a list of the form ((x p) (y q) ...); return a simplifyied form of x^p y^q ...

(defun multiply-algebraic-numbers (l)
  (let ((acc nil) (p) (lk))
    (setq l (mapcar #'(lambda (s) (list (first s) (/ ($num (second s)) ($denom (second s))))) l))
    (setq l (delete-if #'(lambda (s) (equal 1 (first s))) l))
   
    ;; Do x^p * x^q --> x^(p + q).
    (setq l (sort l #'great :key 'car))
   
    (while l
      (setq lk (pop l))
      (setq p (cadr lk))
      (setq lk (car lk))
      (while (and l (like lk (caar l)))
	(setq p (+ p (cadar l)))
	(pop l))
      (if (not (eq p 0)) (push (list lk p) acc)))
   
    ;; Now do x^p * y^p --> (x * y)^p.
    (setq l nil)
    (setq acc (sort acc #'great :key 'cadr))
    (while acc
      (setq lk (pop acc))
      (setq p (cadr lk))
      (setq lk (car lk))
      (while (and acc (equal p (cadar acc)))
	(setq lk (* lk (caar acc)))
	(pop acc))
      (push (list lk (bigfloat-to-maxima p)) l))
    ;(print `(l = ,l))
    (sort l #'great :key 'car)))


;; Bogus
;(defun reduce-by-even-integer (x) x)
	 
(defun bigfloat-to-maxima (x) 
  (let ((xr (maxima::to (bigfloat::realpart x)))
        (xi (maxima::to (bigfloat::imagpart x))))
      (cond ((mzerop xi) xr)
            ((onep xi)
               (list (list 'mplus 'simp) xr '$%i))
            ((mzerop xr)
               (list (list 'mtimes 'simp) xi '$%i))
            (t   
              (setq xi (cons (list 'mtimes 'simp) (sort (list '$%i xi) '$orderlessp)))
		          (cons (list 'mplus 'simp) (sort (list xr xi) '$orderlessp))))))
	
(defun float-or-bigfloat-or-rat-p (x)
  (or (floatp x) ($bfloatp x) ($ratnump x) (eq x '$%i)))

(defun simptimes (l w z)
  (declare (ignore w))
  (let ((inf-terms nil) (mequal-terms nil) (num-prod (bigfloat::to 1))
	      (mrat-terms nil) (algebraic-numbers nil) (matrix-terms nil) 
        (mlist-terms nil) (acc nil) (lk) (taylor-terms nil) 
        (interval-terms nil) (sum-terms nil) (op) (do-expand nil))
    (setq do-expand (or dosimp (and (integerp $expop) (> $expop 0))))
    ;; First, simplify each member of l and flatten. By flatten, I mean do (* a (* b c)) --> (* a b c).
    (setq l (cdr l))
    (dolist (li l)
      (setq li (simplifya li z))  ;; <---  dosimp nil?
      (if (mtimesp li) (setq acc (append acc (cdr li))) (push li acc)))

    ;; Second, step thru the list, multiply the numbers, and collect the extended reals,
    ;; CRE expressions, matrices, and equalites in lists. Push everybody else into the list l.

    ;; dosimp (along with expandflag, expandp, and radexpand) controls expansion.
    (setq l nil)
    (dolist (li acc)
      ;; push all terms of the form m^p where m and p are rational into algebraic-numbers
      (cond ((and nil (mexptp li) (mnump (second li)) ($ratnump (third li)))
	           (push (list (second li) (third li)) algebraic-numbers))
	    
	          ;; When do-expand is true, push all terms that are sums into the list sum-terms.
	          ((and do-expand (mplusp li)) 
               (push li sum-terms))

	         ;; multiply numbers
	        ((or (mnump li) (complex-number-p li #'float-or-bigfloat-or-rat-p))
	           (setq num-prod (bigfloat::* num-prod (bigfloat::to li))))      

	        ;; factor out infrequent cases.
	        ((and (consp li) (consp (car li)) (memq (caar li) '(mequal mrat $matrix mlist $interval)))
	          (setq op (caar li))
	          (cond ((eq op 'mequal)
		                (push li mequal-terms))
	           	    (($taylorp li)
		                (push li taylor-terms))
		              ((eq op 'mrat)
		                (push li mrat-terms))
		              ((eq op '$matrix)
		                (push li matrix-terms))
		             ((eq op '$interval)
		                (push li interval-terms))
		              ((eq op 'mlist)
		                 (if $listarith (push li mlist-terms) (push li acc)))))

	        ;; When $use_extended_real_arithmetic is true, push all extended reals into inf-terms
	    ((and $use_extended_real_arithmetic (member li '($minf $inf $infinity $und $ind)))
	      (push li inf-terms))
	    
	    ;; push everybody else into l
	    (t (push li l))))

    ;; Third, sort the list of terms.
    (setq l (sort l #'great))

    ;;(print `(l = ,l))
  
    ;; Fourth, crunch common terms.
    (setq acc nil)
    (while l
      (setq lk (pop l))
      (setq z lk)
      (while (and l (setq z (mult-common-terms z (car l))))
        	(setq lk z)
	       (pop l))
         (if (complex-number-p lk #'float-or-bigfloat-or-rat-p) 
	           (setq num-prod (bigfloat::* num-prod (bigfloat::to lk))) (push lk acc)))
             
    ;; Fifth, reconstitute algebraic numbers and append these terms to acc; also sort acc.
    (setq num-prod (bigfloat-to-maxima num-prod))
    (setq acc (sort acc '$orderlessp))
    
    ;; Sixth, apply the simplifications *(x) --> x, *() --> 1, 
       
    (setq acc
	     (cond ((null acc) 1)
	           ((null (cdr acc)) (car acc))
		         (t (cons '(mtimes simp) acc))))

    (setq acc (number-times-expr-fast num-prod acc))    	            
 
    (when mequal-terms
	      (setq acc (mult-expr-mequal acc mequal-terms)))
    
    (when mrat-terms
      	(setq acc (mult-expr-mrat acc mrat-terms)))

    (when taylor-terms
	      (setq acc (mult-expr-taylor acc taylor-terms)))

    (when matrix-terms
      	(setq acc (mult-expr-matrix acc matrix-terms)))

    (when mlist-terms
      	(setq acc (mult-expr-mlist acc mlist-terms)))

    ;(when interval-terms
    ;	(setq acc (mult-expr-interval acc interval-terms)))

    (when inf-terms
	      (progn
	        ;(print "Infinite term in product")
	        (setq acc (mult-expr-infinities acc inf-terms))))
         ;(print `(sum-terms ,sum-terms))
    
    (when sum-terms
    	(progn
	     ;(print `(sum-terms ,sum-terms))
	      (setq sum-terms (mapcar #'(lambda (s) (margs s)) sum-terms))
	      (setq sum-terms (cons (list acc) sum-terms))
	      (setq sum-terms (reduce #'(lambda (a b) (mult-lists a b)) sum-terms))
	      (setq acc (simplifya (cons '(mplus) sum-terms) t))))
    
    acc)) 
