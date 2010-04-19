#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Theorem 1. Soundness (pg 331)
(test
 (redex-check* stlc
               (Σ Γ d d_prime e m t)
               (implies (true? (term (coerce (Σ Γ ⊢ d d_prime e ~~> m : t))))
                        (true? (term (type-check ((Γ/append Σ Γ) ⊢ m : t)))))) 
 => #t)

(redex-check* stlc
              (Σ Γ d d_prime e)
              (let* ([m (gensym 'm)]
                     [t (gensym 't)]
                     [cterm (term (coerce (Σ Γ ⊢ d d_prime e ~~> (var ,m) : (var ,t))))])
                (for/and ([ans (in-list (search-relation-successes cterm))])
                  (let ([m-t (hash-ref ans m `(var ,m))]
                        [t-t (hash-ref ans t `(var ,t))])
                    (true? (term (type-check ((Γ/append Σ Γ) ⊢ ,m-t : ,t-t))))))))