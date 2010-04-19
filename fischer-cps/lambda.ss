#lang scheme
(require redex)
(provide lambda
         subst*
         subst
         alpha-equal?)

(define-language lambda
  [e v
     (e e)]
  [v x
     (λ (x) e)]
  [x variable-not-otherwise-mentioned])

(define-metafunction lambda
  subst* : (x ...) (e ...) e -> e
  [(subst* () () e_1)
   e_1]
  [(subst* (x_1 x_r ...)
           (v_1 e_r ...)
           e_1)
   (subst x_1 e_1
          (subst* (x_r ...)
                  (e_r ...)
                  e_1))])

(define-metafunction lambda
  subst : x e e -> e
  [(subst x_1 e_1 (λ (x_1) e_2))
   (λ (x_1) e_2)]
  [(subst x_1 e_1 (λ (x_2) e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (λ (x_new) 
                      (subst x_1 e_1 
                             (subst x_2 x_new e_2)))))]
  [(subst x_1 e_1 x_1)
   e_1]
  [(subst x_1 e_1 x_2)
   x_2
   (side-condition (not (equal? (term x_1) (term x_2))))]
  [(subst x_1 e_1 (e_2 e_3))
   ((subst x_1 e_1 e_2)
    (subst x_1 e_1 e_3))])

;; Alpha equivalence
(define-metafunction lambda
  alpha-vary : e -> e
  [(alpha-vary (λ (x_init) e_body))
   ,(term-let ([x_new (gensym (term x_init))])
              (term (λ (x_new) (subst x_init x_new (alpha-vary e_body)))))]
  [(alpha-vary x_init)
   x_init]
  [(alpha-vary (e_1 e_2))
   ((alpha-vary e_1)
    (alpha-vary e_2))])

(define (alpha-equal? t1 t2)
  (define t1->t2-map (make-hasheq))
  (define alpha=?
    (match-lambda*
      [(list (list) (list))
       #t]
      [(list (list-rest fst1 rst1)
             (list-rest fst2 rst2))
       (and (alpha=? fst1 fst2)
            (alpha=? rst1 rst2))]
      [(list (? symbol? s1)
             (? symbol? s2))
       (match (hash-ref t1->t2-map s1 #f)
         [#f
          (hash-set! t1->t2-map s1 s2)
          #t]
         [s3
          (eq? s2 s3)])]))
  (alpha=? (term (alpha-vary ,t1))
           (term (alpha-vary ,t1))))