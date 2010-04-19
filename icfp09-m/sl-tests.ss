#lang scheme
(require redex
         scheme/package
         "sl.ss"
         "common.ss")

;; Tests
;;; Values
(test-->> -->_sl
          '(/ mt (λ (x) x))
          '(/ mt (λ (x) x)))
(test-->> -->_sl
          '(/ mt ("nil"))
          '(/ mt ("nil")))
(test-->> -->_sl
          '(/ mt ("S" ("0")))
          '(/ mt ("S" ("0"))))
(test-->> -->_sl
          '(/ mt (! "x"))
          '(/ mt (! "x")))

;;; Applications
(test-->> -->_sl 
          '(/ mt ((λ (x) x) ("nil")))
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

;;; match
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("S" n) => n]
                   [("0") => ("0")]))
          '(/ mt ("0")))
(test-->> -->_sl
          '(/ mt (match ("S" ("0"))
                   [("0") => ("0")]
                   [("S" n) => n]))
          '(/ mt ("0")))

; Store match
(test-->> -->_sl
          '(/ mt (letrec (["x" ("S" ("0"))])
                   (match (! "x")
                     [("S" n) => n]
                     [("0") => ("0")])))
          '(/ (snoc mt ["x" -> ("S" ("0"))])
              ("0")))

;; wcm
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) ,(num 2)))
          `(/ mt ,(num 2)))
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) (wcm ([("k") ,(num 3)]) ,(num 2))))
          `(/ mt ,(num 2)))
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) ((λ (x) x) ,(num 2))))
          `(/ mt ,(num 2)))

;; c-c-m
(test-->> -->_sl
          `(/ mt (c-c-m ("k")))
          `(/ mt ("nil")))
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) (c-c-m ("k"))))
          `(/ mt ("cons" ("marks" ("some" ,(num 1))) ("nil"))))
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) (wcm ([("k") ,(num 2)]) (c-c-m ("k")))))
          `(/ mt ("cons" ("marks" ("some" ,(num 2))) ("nil"))))
(test-->> -->_sl
          `(/ mt (wcm ([("k") ,(num 1)]) ((λ (x) x) (wcm ([("k") ,(num 2)]) (c-c-m ("k"))))))
          `(/ mt ("cons" ("marks" ("some" ,(num 1))) ("cons" ("marks" ("some" ,(num 2))) ("nil")))))

(test-->> -->_sl
          `(/ mt (wcm ([("k1") ,(num 1)]) (c-c-m ("k1") ("k2"))))
          `(/ mt ("cons" ("marks" ("some" ,(num 1)) ("none")) ("nil"))))
(test-->> -->_sl
          `(/ mt (wcm ([("k1") ,(num 1)]) (wcm ([("k2") ,(num 2)]) (c-c-m ("k1") ("k2")))))
          `(/ mt ("cons" ("marks" ("some" ,(num 1)) ("some" ,(num 2))) ("nil"))))

;; abort
(test-->> -->_sl
          `(/ mt (abort ,(num 2)))
          `(/ mt ,(num 2)))
(test-->> -->_sl
          `(/ mt ((λ (x) x) (abort ,(num 2))))
          `(/ mt ,(num 2)))

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

;; fact
(package-begin
 (define fact-impl
   `(λ (n)
      ,(:if `((! "=") n ,(num 0))
            (:let 'marks '(c-c-m ("fact"))
                  '(abort marks))
            `(wcm ([("fact") n])
                    ,(:let 'sub1-fact
                           (:let 'sub1 `((! "-") n ,(num 1))
                                 `((! "fact") sub1))
                           `((! "*") n sub1-fact))))))
 (define fact-tr-impl
   `(λ (n a)
      ,(:if `((! "=") n ,(num 0))
            (:let 'marks '(c-c-m ("fact"))
                  '(abort marks))
            `(wcm ([("fact") n])
                    ,(:let 'sub1 `((! "-") n ,(num 1))
                           (:let 'multa `((! "*") n a)
                                 `((! "fact-tr") sub1 multa)))))))
 (define (test-fact n)
   (test-->> -->_sl
             `(/ mt ,(with-arith
                      `(letrec (["fact" ,fact-impl])
                         ((! "fact") ,(num n)))))
             `(/ (snoc ,arith-store ["fact" -> ,fact-impl])
                 ,(lst (build-list n (lambda (i) (term ("marks" ("some" ,(num (- n i)))))))))))
 (define (test-fact-tr n)
   (test-->> -->_sl
             `(/ mt ,(with-arith
                      `(letrec (["fact-tr" ,fact-tr-impl])
                         ((! "fact-tr") ,(num n) ,(num 1)))))
             `(/ (snoc ,arith-store ["fact-tr" -> ,fact-tr-impl])
                 ,(lst (list (term ("marks" ("some" ,(num 1)))))))))
 (for ([i (in-range 1 4)]) (test-fact i))
 (for ([i (in-range 1 4)]) (test-fact-tr i)))

;; call/cc
(test-->> -->_sl
          `(/ mt (call/cc (λ (k) (k ("v")))))
          `(/ mt ("v")))
(test-->> -->_sl
          `(/ mt (call/cc (λ (k) 
                            ((λ (x) ("x"))
                             (k ("v"))))))
          `(/ mt ("v")))

;; call/cc + wcm
(test-->> -->_sl
          `(/ mt (wcm ([("k") ("v1")])
                        ((λ (f) (f ("unit")))
                         (call/cc (λ (k)
                                    (wcm ([("k") ("v2")])
                                           (k (λ (x) (c-c-m ("k"))))))))))
          `(/ mt ("cons" ("marks" ("some" ("v1"))) ("nil"))))

(test-->> -->_sl
          `(/ mt (wcm ([("k") ("v1")])
                        ((λ (f) (f ("unit")))
                         (call/cc (λ (k)
                                    (wcm ([("k") ("v2")])
                                           ((λ (cms)
                                              (k (λ (x) cms)))
                                            (c-c-m ("k")))))))))
          `(/ mt ("cons" ("marks" ("some" ("v1"))) ("cons" ("marks" ("some" ("v2"))) ("nil")))))

(test-results)