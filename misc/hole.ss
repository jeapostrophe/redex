#lang scheme
(require redex
         tests/eli-tester)

(define-language tl-grammar
  [v (cont (hide-hole E))]
  [E hole
     (v ... E)])

(define the-test
  (reduction-relation
   tl-grammar
   [--> (in-hole E_1 (explode))
        (in-hole E_1 1)]))

(test--> the-test 
         (term ((cont hole) (explode)))
         (term ((cont hole) 1)))

(define test-it
  (term-match/single
   tl-grammar
   [(in-hole E_1 (explode))
    (begin (printf "E_1 is: ~S~n" (term E_1))
           (term (in-hole E_1 1)))]))

(test
 (test-it
  (term ((cont hole) (explode))))
 =>
 (term ((cont hole) 1)))