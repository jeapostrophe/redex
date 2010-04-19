#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

; Statements underneath definition 4
(test
 (bool-not (SNA (term (((· ptof : P → (Float → (Float → Float)))
                        ptoi : P → (Int → (Int → Int)))
                       ftoi : Float → Int))
                (term b) (term b))) 
 => #t
 
 (SNA (term (· ftoi : Float → Int))
      (term b) (term b)) 
 => #t)