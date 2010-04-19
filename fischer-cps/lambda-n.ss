#lang scheme
(require redex
         "lambda.ss")
(provide lambda-n
         -->_n
         Eval_n
         test-Eval_n)

(define-extended-language 
  lambda-n lambda
  [E hole
     (E e)])

(define -->_n
  (reduction-relation
   lambda-n
   (--> (in-hole E_1 ((λ (x_arg) e_body) e_arg))
        (in-hole E_1 (subst x_arg e_arg e_body))
        "beta")))

(define (Eval_n M)
  (match (apply-reduction-relation* -->_n M)
    [(list fst)
     fst]
    [(list)
     (error 'Eval_n "Term did not reduce: ~S" M)]
    [(list all ...)
     (error 'Eval_n "Term had multiple reductions: ~S" M)]))

(define (test-Eval_n term expected)
  (define actual (Eval_n term))
  (unless (alpha-equal? actual expected)
    (error 'test-Eval_n "Evaluation error~n~S~nevaluated to~n~S~n, not~n~S" term actual expected)))
                     