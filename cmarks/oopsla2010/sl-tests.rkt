#lang racket
(require redex
         scheme/package
         "sl.rkt"
         "common.rkt")

;; Tests
;;; Values
(test-->> -->_sl
          '(/ mt (λ (x) x))
          '(/ mt (λ (x) x)))
(test-->> -->_sl
          '(/ mt (unsafe-λ (x) x))
          '(/ mt (unsafe-λ (x) x)))
(test-->> -->_sl
          '(/ mt ("nil"))
          '(/ mt ("nil")))
(test-->> -->_sl
          '(/ mt ("S" ("0")))
          '(/ mt ("S" ("0"))))
(test-->> -->_sl
          '(/ mt (cont hole))
          '(/ mt (cont hole)))
(test-->> -->_sl
          '(/ mt (! "x"))
          '(/ mt (! "x")))

;;; Applications
(test-->> -->_sl 
          '(/ mt ((λ (x) x) ("nil")))
          '(/ mt ("nil")))
(test-->> -->_sl 
          '(/ mt ((unsafe-λ (x) x) ("nil")))
          '(/ mt ("nil")))

;;; Store applications
(test-->> -->_sl
          '(/ (snoc mt ["x" -> (λ (x) ("nil"))])
              ((! "x") ("0")))
          '(/ (snoc mt ["x" -> (λ (x) ("nil"))])
              ("nil")))

;;; Letrec
(test-->> -->_sl
          '(/ mt (letrec (["x" (λ (x) ("nil"))])
                   ("foo")))
          '(/ (snoc mt ["x" -> (λ (x) ("nil"))])
              ("foo")))
(test-->> -->_sl
          '(/ mt (letrec (["x" (λ (x) ("nil"))])
                   ((! "x") ("0"))))
          '(/ (snoc mt ["x" -> (λ (x) ("nil"))])
              ("nil")))
(test-->> -->_sl
          '(/ mt (letrec (["x" (unsafe-λ (x) ("nil"))])
                   ("foo")))
          '(/ (snoc mt ["x" -> (unsafe-λ (x) ("nil"))])
              ("foo")))
(test-->> -->_sl
          '(/ mt (letrec (["x" (unsafe-λ (x) ("nil"))])
                   ((! "x") ("0"))))
          '(/ (snoc mt ["x" -> (unsafe-λ (x) ("nil"))])
              ("nil")))

;;; match
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("0" n) => ("1")]
                   [("S" n) => n]))
          '(/ mt ("0")))
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("S" n) => n]
                   [("0") => ("1")]))
          '(/ mt ("0")))
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("0") => ("1")]
                   [("S" n) => n]))
          '(/ mt ("0")))
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("0") => ("0")]
                   [else => ("default")]))
          '(/ mt ("default")))
(test-->> -->_sl
          `(/ mt ,(:let 'x '(call/cc (λ (x) x))
                        `(match x
                           [("0") => ("0")]
                           [else => ("default")])))
          '(/ mt ("default")))


; Store match
(test-->> -->_sl
          '(/ mt (letrec (["x" ("S" ("0"))])
                   (match (! "x")
                     [("S" n) => n]
                     [("0") => ("0")])))
          '(/ (snoc mt ["x" -> ("S" ("0"))])
              ("0")))

; Call/cc
(test-->> -->_sl
          '(/ mt (call/cc (λ (x) x)))
          (term (/ mt (cont hole))))
(test-->> -->_sl
          '(/ mt (call/cc (λ (esc)
                            ((λ (x) ("S" ("S" ("S" x))))
                             (call/cc (λ (k) (esc k)))))))
          (term (/ mt (cont ((λ (x) ("S" ("S" ("S" x)))) hole)))))

;;; Continuation invocation
(test-->> -->_sl
          (term (/ mt ((cont hole) ("0"))))
          '(/ mt ("0")))
(test-->> -->_sl
          (term (/ mt ((cont ((λ (x) ("S" x)) hole)) ("0"))))
          '(/ mt ("S" ("0"))))

;; arith
(test-->> -->_sl
          `(/ mt ,(:let 'x (num 1) 'x))
          `(/ mt ,(num 1)))
(test-->> -->_sl
          `(/ mt ,(with-arith (num 1)))
          `(/ ,arith-store ,(num 1)))
(test-->> -->_sl
          `(/ mt ,(with-arith `((! "+") ,(num 1) ,(num 1))))
          `(/ ,arith-store ,(num 2)))
(test-->> -->_sl
          `(/ mt ,(with-arith `((! "*") ,(num 2) ,(num 2))))
          `(/ ,arith-store ,(num 4)))
(test-->> -->_sl
          `(/ mt ,(with-arith `((! "=") ,(num 2) ,(num 2))))
          `(/ ,arith-store ("#t")))
(test-->> -->_sl
          `(/ mt ,(with-arith `((! "=") ,(num 2) ,(num 3))))
          `(/ ,arith-store ("#f")))
(test-->> -->_sl
          `(/ mt ,(with-arith `((! "-") ,(num 3) ,(num 2))))
          `(/ ,arith-store ,(num 1)))
(test-->> -->_sl
          `(/ mt ,(with-arith (:if '("#t") (num 1) (num 2))))
          `(/ ,arith-store ,(num 1)))
(test-->> -->_sl
          `(/ mt ,(with-arith (:if '("#f") (num 1) (num 2))))
          `(/ ,arith-store ,(num 2)))

;; callcc puzzles
(test-->> -->_sl
          `(/ ,arith-store ((λ (tmp) ((! "+") ,(num 1) tmp))
                            (call/cc (λ (k) 
                                       ((λ (tmp) ((! "+") ,(num 2) tmp))
                                        (k ,(num 3)))))))
          `(/ ,arith-store ,(num 4)))

;; fact
(package-begin
 (define fact-impl
   `(λ (n)
      ,(:if `((! "=") n ,(num 0))
            (num 1)
            (:let 'sub1-fact
                  (:let 'sub1 `((! "-") n ,(num 1))
                        `((! "fact") sub1))
                  `((! "*") n sub1-fact)))))
 (define fact-tr-impl
   `(λ (n a)
      ,(:if `((! "=") n ,(num 0))
            'a
            (:let 'sub1 `((! "-") n ,(num 1))
                  (:let 'multa `((! "*") n a)
                        `((! "fact-tr") sub1 multa))))))
 (define (test-fact n)
   (test-->> -->_sl
             `(/ mt ,(with-arith
                         `(letrec (["fact" ,fact-impl])
                            ((! "fact") ,(num n)))))
             `(/ (snoc ,arith-store ["fact" -> ,fact-impl]) ,(num (fact n)))))
 (define (test-fact-tr n)
   (test-->> -->_sl
             `(/ mt ,(with-arith
                         `(letrec (["fact-tr" ,fact-tr-impl])
                            ((! "fact-tr") ,(num n) ,(num 1)))))
             `(/ (snoc ,arith-store ["fact-tr" -> ,fact-tr-impl]) ,(num (fact n)))))
 (for ([i (in-range 0 4)]) (test-fact i))
 (for ([i (in-range 0 4)]) (test-fact-tr i)))

(test-->> -->_sl
          `(/ mt ,(with-safe
                      (:let 'l 
                            `((! "unsafe-map")
                              (λ (x) (call/cc (λ (k) k)))
                              ("cons" ,(num 1) ("cons" ,(num 2) ("nil"))))
                            `(match l
                               [("cons" k1 l1)
                                =>
                                (match l1
                                  [("cons" k2 l2)
                                   =>
                                   (match k2
                                     [("one") => ("done")]
                                     [else =>
                                           (match l2
                                             [("nil")
                                              =>
                                              (k2 ("one"))])])])]))))
          
          `(/ ,safe-store 
              ("done")))

(test-results)
