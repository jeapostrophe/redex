#lang scheme
(require redex
         "lambda.ss"
         "lambda-v.ss"
         "lambda-n.ss"
         "cps.ss"
         "church.ss")

; XXX test the output

(for ([i (in-range 0 4)])
  (printf "Number: ~a~n" i)
  (test-CPS (term ,(Num i))))
(collect-garbage)

(for ([i (in-range 0 3)])
  (printf "Succ: ~a~n" i)
  (test-CPS (term (,succ ,(Num i)))))
(collect-garbage)

(for* ([i (in-range 0 2)]
       [j (in-range 0 2)])
  (printf "Plus: ~a ~a~n" i j)
  (test-CPS (term ((,plus ,(Num i)) ,(Num j)))))
(collect-garbage)

(for* ([i (in-range 0 2)]
       [j (in-range 0 2)])
  (printf "Mult: ~a ~a~n" i j)
  (test-CPS (term ((,mult ,(Num i)) ,(Num j)))))
(collect-garbage)

(for ([i (in-range 0 3)])
  (printf "Pred: ~a~n" i)
  (test-CPS (term (,pred ,(Num i)))))
(collect-garbage)