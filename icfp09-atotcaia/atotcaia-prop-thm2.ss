#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Theorem 2. Sufficiency (pg 331)
(test
 (redex-check* stlc
               (Σ Γ d d_prime m t)
               (implies (true? (term (type-check (Γ ⊢ m : t))))
                        (true? (term (coerce (Σ Γ ⊢ d d_prime m ~~> m : t)))))) 
 => #t)
