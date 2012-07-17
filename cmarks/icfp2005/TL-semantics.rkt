#lang racket

(require "TL-syntax.rkt"
         redex)

(provide -->TL χ)

(define TL-expr? (redex-match TL e))

(define -->TL
  (reduction-relation
   TL #:domain (Σ / e)
   (--> (Σ / (in-hole E ((λ (x ..._1) e) v ..._1)))
        (Σ / (in-hole E (subst-n (x v) ... e)))
        "beta")
   (--> (Σ / (in-hole E (match (K v ...) l ...)))
        (Σ / (in-hole E (subst-n (x v) ... e)))
        ; The match must be unique, according to Fig. 5
        (where ([(K x ...) e]) (matches (K v ...) l ...))
        "match")
   (--> (Σ / (in-hole E (letrec ([σ v] ...) e)))
        ((store-set Σ [σ ↦ v] ...) / (in-hole E e))
        "letrec")
   (--> (Σ / (in-hole E (σ v ..._0)))
        (Σ / (in-hole E (subst-n (x v) ... e)))
        (where (λ (x ..._0) e) (store-lookup Σ σ))
        "sig beta")
   (--> (Σ / (in-hole E (match σ l ...)))
        (Σ / (in-hole E (match (store-lookup Σ σ) l ...)))
        "sig match")
   (--> (Σ / (in-hole E (w-c-m v_k v_1
                               (in-hole C (w-c-m v_k v_2 e)))))
        (Σ / (in-hole E (w-c-m v_k v_2 (in-hole C e))))
        (side-condition (term (no-dup-keys C (v_k))))
        "wcm idem")
   (--> (Σ / (in-hole E (w-c-m v_k v_1 v_2)))
        (Σ / (in-hole E v_2))
        "wcm return")
   (--> (Σ / (in-hole E (c-c-m [v ...])))
        (Σ / (in-hole E (χ (v ...) E ("nil"))))
        "ccm")
   (--> (Σ / (in-hole E (abort e)))
        (Σ / e)
        "abort")))

(define-metafunction TL
  [(matches (K v ...)) ()]
  [(matches 
    (K v ..._1)
    [(K x ..._1) e]
    l ...)
   ([(K x ...) e] l_i ...)
   (where (l_i ...) (matches (K v ...) l ...))]
  [(matches 
    (K v ..._1)
    l_0 l_1 ...)
   (l_i ...)
   (where (l_i ...) (matches (K v ...) l_1 ...))])

(define-metafunction TL
  [(store-set Σ) Σ]
  [(store-set Σ [σ_0 ↦ v_0] [σ_1 ↦ v_1] ...)
   (store-set (Σ [σ_0 ↦ v_0]) [σ_1 ↦ v_1] ...)])

(define-metafunction TL
  [(store-lookup (Σ [σ ↦ v]) σ) v]
  [(store-lookup (Σ [σ_1 ↦ v]) σ_2)
   (store-lookup Σ σ_2)])

(define-metafunction TL
  [(χ (v_0 ...) E)
   (χ (v_0 ...) E ("nil"))]
  [(χ (v_0 ...) hole v_l) ("cons" v_l ("nil"))]
  [(χ (v_0 ...) (v_i ... E) v_l)
   ("cons" v_l (χ (v_0 ...) E ("nil")))]
  [(χ (v_0 ... v_k v_k+1 ...) (w-c-m v_k v_v E) v_l)
   (χ (v_0 ... v_k v_k+1 ...) E ("cons" ("cons" v_k v_v) v_l))]
  [(χ (v_0 ...) (w-c-m v_k v_v E) v_l)
   (χ (v_0 ...) E v_l)])

(define-metafunction TL
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) any_3])

(define-metafunction TL
  ;; x_1 bound, so don't continue in body 
  [(subst x_1 any_1 (λ (x_2 ... x_1 x_3 ...) any_2))
   (λ (x_2 ... x_1 x_3 ...) any_2)]
  ;; general purpose capture avoiding case 
  [(subst x_1 any_1 (λ (x_2 ...) any_2))
   (λ (x_new ...) (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_2)))
   (where (x_new ...) ,(variables-not-in (term (x_1 any_1 any_2)) (term (x_2 ...))))]
  ;; replace x_1 with e_1 
  [(subst x_1 any_1 x_1) any_1]
  ;; x_1 and x_2 are different, so don't replace 
  [(subst x_1 any_1 x_2) x_2]
  ;; match
  [(subst x_1 any_1 (match a [(K_0 x_0 ...) e_0] ...))
   (match (subst x_1 any_1 a)
     [(K_0 x_0’ ...) e_0’] 
     ...)
   (where 
    ((λ (x_0’ ...) e_0’) ...)
    ((subst x_1 any_1 (λ (x_0 ...) e_0)) ...))]
  ;; ref
  [(subst x any σ) σ]
  ;; the last cases cover all other expressions 
  [(subst x_1 any_1 (any_2 ...)) ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction TL
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3)
   (subst-vars (x_1 any_1) (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])
