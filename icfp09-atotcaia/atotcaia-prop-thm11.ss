#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Theorem 11
(test
 (redex-check* stlc
               (Σ Γ m_e t)
               (implies (and (BaseCoercions (term Σ))
                             (true? (term (type-check ((Γ/append Σ Γ) ⊢ m_e : t)))))
                        (let ([m (gensym 'm)]
                              [t_prime (gensym 't_prime)])
                          (any (search-relation-successes (term (coerce (Σ Γ ⊢ r s m_e ~~> (var ,m) : (var ,t_prime)))))
                               (lambda (ans)
                                 (define m-t (hash-ref ans m))
                                 (define t_prime-t (hash-ref ans t_prime))
                                 (define c (gensym 'c))
                                 (true? (term (generate (Σ ⊢ ,t_prime-t <I s ~~> (var ,c)))))))))))
