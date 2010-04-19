#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Theorem 13 (pg 336)
(test
 (redex-check* stlc
               (Σ Γ)
               (implies (bool-and (NAC_π (term r) (term Σ))
                                  (NAC_T (term r) (term Σ))
                                  (NAC^*_π (term s) (term Σ)))
                        (bool-and (NAC_π (term s) (term Σ))))))