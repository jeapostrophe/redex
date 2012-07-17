#lang racket

(require redex)
(provide TL no-dup-keys)

(define-language TL
  (e a
     (a ... e)
     (letrec ([σ v] ...) e)
     (w-c-m a a e)
     (c-c-m [a ...])
     (match a l ...)
     (abort e))
  
  (l [(K x ...) e])
  (a (λ (x ...) e)
     σ
     x
     (K a ...))
  (w v
     x)
  (v (λ (x ...) e)
     (K v ...)
     σ)
  
  (x variable-not-otherwise-mentioned)
  (σ (ref variable))
  
  (Σ ∅
     (Σ [σ ↦ v]))
  
  (K string)

  (D hole
     (w-c-m v v E)
     (v ... E))
  (E (side-condition D_1 (term (no-dup-keys D_1 ()))))
  (C (w-c-m v v C)
     hole))

(define-metafunction TL
  [(no-dup-keys hole (v ...)) 
   #t]
  [(no-dup-keys (w-c-m v_i v D) (v_0 ... v_i v_i+1 ...))
   #f]
  [(no-dup-keys (w-c-m v_i v D) (v_0 ...))
   (no-dup-keys D (v_i v_0 ...))]
  [(no-dup-keys (v ... D) (v_0 ...))
   (no-dup-keys D ())])
