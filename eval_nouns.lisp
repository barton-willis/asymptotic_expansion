(defun $apply_nouns (e ops)
  "Recursively applies noun transformations to an expression `e` 
   based on the operators in `ops`. If a noun transformation is found, 
   it applies `$verbify` to convert it before further processing."

  (unless (and ($listp ops) (every #'$mapatom (cdr ops)))
    (merror (intl:gettext "The second argument to 'apply_nouns' must be a list of mapatoms.")))

  (cond 
    (($mapatom e) e)
    (t
     (let ((fn (get (mop e) 'noun)))
       (cond 
         ((and fn (member fn (cdr ops)))
          (mfuncall '$apply ($verbify fn)
                    (fapply 'mlist 
                            (mapcar (lambda (q) ($apply_nouns q ops)) (cdr e)))))
         (t
          (recur-apply (lambda (q) ($apply_nouns q ops)) e)))))))