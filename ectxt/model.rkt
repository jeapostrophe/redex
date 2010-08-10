#lang racket/load

(module okay:simple-contexts racket
  (require redex)
  
  (define-language ectxt
    [e a
       (e e)]
    [E the-hole
       (E e)
       (e E)]
    [a variable-not-otherwise-mentioned])
  
  (define (decomposer t)
    (list* (list 'the-hole t)
           (match t
             [(list e_1 e_2)
              (append
               (for/list ([d_lhs (in-list (decomposer e_1))])
                 (match-define (list E_lhs p_lhs) d_lhs)
                 (list (list E_lhs e_2) p_lhs))
               (for/list ([d_rhs (in-list (decomposer e_2))])
                 (match-define (list E_rhs p_rhs) d_rhs)
                 (list (list e_1 E_rhs) p_rhs)))]
             [_
              empty])))
  
  (define plugger 
    (term-match/single
     ectxt
     [(the-hole e_p)
      (term e_p)]
     [((E e_2) e_p)
      (term (,(plugger (term (E e_p))) e_2))]
     [((e_1 E) e_p)
      (term (e_1 ,(plugger (term (E e_p)))))]))
  
  (define (property-1 t)
    (for/and ([d (in-list (decomposer t))])
      (equal? t (plugger d))))
  
  (printf "\tProperty 1:\n")
  (redex-check ectxt e (property-1 (term e))))

(printf "Expressions without holes:\n")
(require 'okay:simple-contexts)
(newline)

(module broken:complicated-contexts racket
  (require redex)
  
  (define-language ectxt
    [e a
       the-hole
       (e e)]
    [E e]
    [a variable-not-otherwise-mentioned])
  
  (define (decomposer t)
    (list* (list 'the-hole t)
           (match t
             [(list e_1 e_2)
              (append
               (for/list ([d_lhs (in-list (decomposer e_1))])
                 (match-define (list E_lhs p_lhs) d_lhs)
                 (list (list E_lhs e_2) p_lhs))
               (for/list ([d_rhs (in-list (decomposer e_2))])
                 (match-define (list E_rhs p_rhs) d_rhs)
                 (list (list e_1 E_rhs) p_rhs)))]
             [_
              empty])))
  
  (define plugger 
    (term-match/single
     ectxt
     [(a e_p)
      (term a)]
     [(the-hole e_p)
      (term e_p)]
     [((e_1 e_2) e_p)
      (term (,(plugger (term (e_1 e_p))) ,(plugger (term (e_2 e_p)))))]))
  
  (define (property-1 t)
    (for/and ([d (in-list (decomposer t))])
      (equal? t (plugger d))))
  
  (printf "\tProperty 1:\n")
  (redex-check ectxt e (property-1 (term e))))

(printf "Expressions with holes:\n")
(require 'broken:complicated-contexts)
(newline)

(module complicated-contexts racket
  (require redex)
  
  (define-language ectxt
    [e a
       the-hole
       (hide-hole e)
       (e e)]
    [a variable-not-otherwise-mentioned])
  
  (define (decomposer t)
    (list* (list 'the-hole t)
           (match t
             [(list 'hide-hole e_1)
              empty]
             [(list e_1 e_2)
              (append
               (for/list ([d_lhs (in-list (decomposer e_1))])
                 (match-define (list E_lhs p_lhs) d_lhs)
                 (list (list E_lhs (list 'hide-hole e_2)) p_lhs))
               (for/list ([d_rhs (in-list (decomposer e_2))])
                 (match-define (list E_rhs p_rhs) d_rhs)
                 (list (list (list 'hide-hole e_1) E_rhs) p_rhs)))]
             [_
              empty])))
  
  (define plugger
    (term-match/single
     ectxt
     [(a any_p)
      (term a)]
     [(the-hole any_p)
      (term any_p)]
     [((hide-hole e) any_p)
      (term e)]
     [((e_1 e_2) any_p)
      (term (,(plugger (term (e_1 any_p))) ,(plugger (term (e_2 any_p)))))]))
  
  (define (property-1 t)
    (for/and ([d (in-list (decomposer t))])      
      (equal? t (plugger d))))
  
  (printf "\tProperty 1:\n")
  (redex-check ectxt e 
               (property-1 (term e)))
  
  (define (property-2 E1 E2 e)
    (equal? (plugger (list E1 (plugger (list E2 e))))
            (plugger (list (plugger (list E1 E2)) e))))
  
  (printf "\tProperty 2:\n")
  (redex-check ectxt (e_1 e_2 e)
               (property-2 (term e_1) (term e_2) (term e))))

(printf "Expressions with holes & hide-hole:\n")
(require 'complicated-contexts)
(newline)
