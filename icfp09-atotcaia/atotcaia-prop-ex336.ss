#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; pg 336 (rhs of column)
(define Fig7-Σ 
  (term
   ((((((((· Bo : Bool → Dyn) Bn : Dyn → Bool)
         I : Int → Dyn) In : Dyn → Int)
       F : (Dyn → Dyn) → Dyn) Fn : Dyn → (Dyn → Dyn))
     P : (Dyn × Dyn) → Dyn) Pn : Dyn → (Dyn × Dyn))))

; XXX
#;(test
 (NAC_× 'r Fig7-Σ)
 (NAC_app 'r 's Fig7-Σ)
 (NAC_π 'r Fig7-Σ)
 (NAC_π 's Fig7-Σ)
 (NAC_T 'r Fig7-Σ) => #f)