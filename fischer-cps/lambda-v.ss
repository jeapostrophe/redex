#lang scheme
(require redex
         "lambda.ss")
(provide lambda-v
         -->_v
         Eval_v
         test-Eval_v)

(define-extended-language 
  lambda-v lambda
  [E hole
     (v E)
     (E e)])

(define -->_v
  (reduction-relation
   lambda-v
   (--> (in-hole E_1 ((λ (x_arg) e_body) v_arg))
        (in-hole E_1 (subst x_arg v_arg e_body))
        "beta-v")))

(define (Eval_v M)
  (match (apply-reduction-relation* -->_v M)
    [(list fst)
     fst]
    [(list)
     (error 'Eval_v "Term did not reduce: ~S" M)]
    [(list all ...)
     (error 'Eval_v "Term had multiple reductions: ~S" M)]))

(define (test-Eval_v term expected)
  (define actual (Eval_v term))
  (unless (alpha-equal? actual expected)
    (error 'test-Eval_v "Evaluation error~n~S~nevaluated to~n~S~n, not~n~S" term actual expected)))