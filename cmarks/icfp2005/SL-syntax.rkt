#lang racket

(require redex)
(provide SL)

(define-language SL
  (e a
     (a ... e)
     (letrec ([σ v] ...) e)
     (match a l ...)
     (call/cc w))
  
  (l [(K x ...) e])
  (a (λ (x ...) e)
     σ
     x
     (K a ...)
     (κ (hide-hole E)))
  (w v
     x)
  (v (λ (x ...) e)
     (K v ...)
     σ
     (κ (hide-hole E)))
  
  (x variable-not-otherwise-mentioned)
  (σ (ref variable))
  
  (Σ ∅
     (Σ [σ ↦ v]))

  (E hole
     (v ... E))
  
  (K string))

