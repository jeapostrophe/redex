#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Theorem 8. Strong non-ambiguity.
(test
 (redex-check* stlc
               (Σ d d_prime)
               (equiv (SNA (term Σ) (term d) (term d_prime))
                      (bool-and (NAC_π (term d) (term Σ))
                                (NAC_π (term d_prime) (term Σ))
                                (NAC_× (term d) (term Σ))
                                (NAC_app (term d) (term d_prime) (term Σ)))))
 =>
 #t)
