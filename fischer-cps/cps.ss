#lang scheme
(require redex
         "lambda.ss"
         "lambda-v.ss"
         "lambda-n.ss"
         tests/eli-tester)
(provide test-CPS)

(define-metafunction lambda-v
  F : e -> e
  [(F v_1)
   ,(term-let ([x_k (variable-not-in (term v_1) 'k)])
              (term (λ (x_k) (x_k (Psi v_1)))))]
  [(F (e_m e_n))
   ,(term-let ([(x_k x_m x_n) (variables-not-in (term (e_m e_n)) '(k m n))])
              (term 
               (λ (x_k)
                 ((F e_m)
                  (λ (x_m)
                    ((F e_n)
                     (λ (x_n)
                       ((x_m x_k) x_n))))))))])

(define-metafunction lambda-v
  Psi : v -> v
  [(Psi x_1)
   x_1]
  [(Psi (λ (x_arg) e_m))
   ,(term-let ([x_k (variable-not-in (term (x_arg e_m)) 'k)])
              (term (λ (x_k)
                      (λ (x_arg)
                        ((F e_m) x_k)))))])

(test
 (term (F ((λ (x) x) (y y)))) =>
 (term (λ (k) ((λ (k) (k (λ (k) (λ (x) ((λ (k) (k x)) k)))))
               (λ (m) ((λ (k) ((λ (k) (k y)) (λ (m) ((λ (k) (k y)) (λ (n) ((m k) n))))))
                       (λ (n) ((m k) n))))))))

(define (CPS M)
  (term ((F ,M) (λ (x) x))))

(define (Simulation M)
  (define M_cps (CPS M))
  (define M_cps_eval (Eval_n M_cps))
  (define M_eval (Eval_v M))
  (define M_eval_Psi (term (Psi ,M_eval)))
  (unless (alpha-equal? M_eval_Psi M_cps_eval)
    (error 'Simulation "On term~n~S~nwith CPS~n~S~nand CPS eval~n~S~nand normal eval~n~S~nand Psi eval~n~S"
           M M_cps M_cps_eval M_eval M_eval_Psi)))

(define (Indifference M)
  (define M_cps (CPS M))
  (define v_eval (Eval_v M_cps))
  (define n_eval (Eval_n M_cps))
  (unless (alpha-equal? v_eval n_eval)
    (error 'Indifference "On term~n~S~nwith CPS~n~S~nEval_v~n~S~nEval_n~n~S~n"
           M M_cps v_eval n_eval)))

(define (test-CPS M)
  (Simulation M)
  (Indifference M))