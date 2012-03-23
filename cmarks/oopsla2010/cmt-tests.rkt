#lang racket
(require redex
         "common.rkt"
         "tl.rkt"
         "cmt.rkt")

(require tests/eli-tester)
(test
 ;; Variables and Values
 (term (CMT-a z)) => (term z)
 (term (CMT-a (! "foo"))) => (term (! "foo"))
 (term (CMT-a (λ (x) z))) =>  (term (λ (x) (wcm ((("safe-call?") ("#t"))) z)))
 (term (CMT-a (unsafe-λ (x) z))) =>  (term (λ (x) z))
 
 (term (CMT-a ("nil"))) => (term ("nil"))
 (term (CMT-a ("cons" x ("nil")))) => (term ("cons" x ("nil")))
 
 ;; Redexes
 (term (CMT-r (f x y))) => (term (wcm ((("safe-call?") ("#f"))) (f x y)))
 
 (term (CMT-r (letrec (["x" ("nil")]) z))) =>
 (term (letrec (["x" ("nil")]) z))
 
 (term (CMT-r (call/cc f))) =>
 (term ((! "call/cc") f))
 
 ;; Contexts
 (term (CMT-EE hole)) => (term hole)
 
 (term (CMT-EE (("f") ("y") hole))) => 
 (term ((λ (x) (("f") ("y") x)) (wcm ((("square") (λ (x) (("f") ("y") x)))) hole)))
 
 ;; Compositions + Whole Programs
 (term (CMT-e (("f") ("y") (call/cc (λ (k) (k z)))))) =>
 (term
  ((λ (x) (("f") ("y") x)) 
   (wcm ((("square") (λ (x) (("f") ("y") x))))
        ((! "call/cc")
         (λ (k) (wcm ((("safe-call?") ("#t")))
                     (wcm ((("safe-call?") ("#f")))
                          (k z))))))))
 
 ;; Sub-units of big test
 (term (CMT-e ((! "+") ,(num 1) tmp))) =>
 (term (wcm ((("safe-call?") ("#f"))) ((! "+") ("S" ("0")) tmp))))

;;; Running the resulting programs
(define (CMT--> sl-version expected-ans mode)
  (define the-callcc
    (case mode
      [(unsafe) callcc-impl]
      [(safe) safe-callcc-impl]))
  (define tl-version
    (CMT sl-version mode))
  (define correct-store
    (term (snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc (snoc mt ("resume" -> ,resume-impl)) ("call/cc" -> ,the-callcc)) ("=" -> (CMT-e ,=-impl))) ("+" -> (CMT-e ,+-impl))) ("-" -> (CMT-e ,--impl))) ("*" -> (CMT-e ,*-impl))) ("if" -> (CMT-e ,if-impl))) ("unsafe-map" -> (CMT-e ,unsafe-map-impl))) ("all-safe?" -> (CMT-e ,all-safe?-impl)))))
  (define the-term
    (term (/ mt ,tl-version)))
  #;(traces -->_tl the-term)
  (test-->> -->_tl the-term
            (term (/ ,correct-store ,expected-ans))))

(define t1
  `(call/cc (λ (k) 
              ((λ (tmp) ((! "+") ,(num 2) tmp))
               (k ,(num 3))))))
(CMT--> t1 (num 3) 'safe)
(CMT--> t1 (num 3) 'unsafe)

(define t2
  `((λ (tmp) ((! "+") ,(num 1) tmp))
    (call/cc (λ (k) 
               ((λ (tmp) ((! "+") ,(num 2) tmp))
                (k ,(num 3)))))))
(CMT--> t2 (num 4) 'safe)
(CMT--> t2 (num 4) 'unsafe)

(define t3
  `((λ (f)
      ,(:let 'x `(f ,(num 2))
             `((! "+") x ,(num 1))))
    (λ (y) (call/cc (λ (k) (k ,(num 3)))))))
(CMT--> t3 (num 4) 'safe)
(CMT--> t3 (num 4) 'unsafe)

(define t4
  `((unsafe-λ (f)
              ,(:let 'x `(f ,(num 2))
                     `((! "+") x ,(num 1))))
    (λ (y) (call/cc (λ (k) (k ,(num 3)))))))
(CMT--> t4 (num 3) 'unsafe)
(CMT--> t4 '("unsafe context") 'safe)

(test-results)
