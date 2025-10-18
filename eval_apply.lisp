(defmfun $eval_nouns (e &optional nounforms)
    (cond (($mapatom e) e)
          (t
            (let* ((op (car e)) (fn (get 'noun op)))
              (if (and fn (member op nounforms))
                       (fapply fn (mapcar #'(lambda (q) ($eval_nouns q nounforms)) (cdr e)))
                       (recur-apply #'(lambda (q) ($eval_nouns q nounforms)) e))))))