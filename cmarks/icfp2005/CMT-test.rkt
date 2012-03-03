#lang racket

(require "CMT.rkt"
         "SL-syntax.rkt"
         "SL-semantics.rkt"
         "TL-syntax.rkt"
         "TL-semantics.rkt"
         "common.rkt"
         "test-util.rkt"
         redex)

(define-syntax (test-translation stx)
  (syntax-case stx ()
    [(_ expr)
     #`(with-handlers ([exn:fail?
                        (λ (exn)
                          #,(syntax/loc stx 
                              (test-equal (format "~a: ~a" 'expr (exn-message exn))
                                          (format "~a: ~a" 'expr ""))))])
         (let ([e (term expr)])
           (let ([v ((make-eval -->SL (redex-match SL v))
                     (term (∅ / ,e)))]
                 [u ((make-eval -->TL (redex-match TL v))
                     (term (∅ / (translate ,e))))])
             #,(syntax/loc stx (test-equal u v)))))]))

(test-translation
 ((λ (x) ("S" x))
  (call/cc (λ (k) (k ("Z"))))))

; application and match translation redexes allow variables
; in datatype instances
(test-translation
 (λ (x) (x ("k" x))))
(test-translation
 (λ (x) (match ("k" x) [("k" x) x])))

(test-->>
 -->TL
 #:cycles-ok
 (term
  (∅
   /
   (translate
    ((λ (t) (t t))
     (call/cc (λ (x) (call/cc x))))))))

(test-translation
 ((λ (bh)
    ((λ (x y) ("pair" x y))
     bh
     (λ (x) x)))
  (letrec ([(ref bh) (ref bh)]) (ref bh))))

(test-TL-result
 (make-store [reverse ,TL-reverse])
 (,TL-equal? ("1") ("1"))
 ("true"))

(test-TL-result
 (make-store [reverse ,TL-reverse])
 (,TL-equal? ("1") ("2"))
 ("false"))

(test-TL-result
 (make-store [equal? ,TL-equal?] [reverse ,TL-reverse] [map-set ,map-set])
 ((ref map-set) ("nil") ("1") ("a"))
 ("cons" ("cons" ("1") ("a")) ("nil")))

(test-TL-result
 (make-store [equal? ,TL-equal?] [reverse ,TL-reverse] [map-set ,map-set])
 ((ref map-set) ("cons" ("cons" ("1") ("a"))
                        ("cons" ("cons" ("2") ("b"))
                                ("nil")))
                ("2") ("c"))
 ("cons" ("cons" ("1") ("a"))
         ("cons" ("cons" ("2") ("c"))
                 ("nil"))))

(test-TL-result
 (make-store [c-w-i-c-m ,c-w-i-c-m] [reverse ,TL-reverse])
 (w-c-m ("a") ("1")
        ((λ (x) x)
         ((ref c-w-i-c-m) ("a") (λ (x) x) ("2"))))
 ("2"))

(test-TL-result
 (make-store [c-w-i-c-m ,c-w-i-c-m] [reverse ,TL-reverse])
 (w-c-m ("a") ("1")
        ((ref c-w-i-c-m) ("a") (λ (x) ("b" x)) ("dontcare")))
 ("b" ("1")))

(test-TL-result
 (make-store [restore-marks ,restore-marks])
 ((ref restore-marks)
  ("cons" ("cons" ("a") ("1"))
          ("cons" ("cons" ("b") ("2"))
                  ("nil")))
  (λ () (c-c-m [("a") ("b")])))
 ("cons"
  ("cons" ("cons" ("b") ("2"))
          ("cons" ("cons" ("a") ("1"))
                  ("nil")))
  ("nil")))

;; Variables and Values
(test-equal (term (CMT/a z)) (term z))
(test-equal (term (CMT/a (ref foo))) (term (ref foo)))
(test-equal (term (CMT/a (λ (x) z))) (term (λ (x) z)))

(define TL-empty-cont
  (term (λ (x) 
          (abort 
           ((ref resume)
            ("cons"
             ("cons" ("nil"))
             ("nil"))
            x)))))
(test-equal (term (CMT/a (κ hole))) TL-empty-cont)

(test-equal 
 (term (CMT/a (κ ((ref f) (ref y) hole))))
 (term (λ (x1) 
         (abort
          ((ref resume)
           ("cons"
            ("cons" ("nil"))
            ("cons"
             ("cons"
              ("cons" 
               ("cons" ("square") (λ (x) ((ref f) (ref y) x)))
               ("nil")))
             ("nil")))
           x1)))))

(test-equal (term (CMT/a ("nil"))) (term ("nil")))
(test-equal (term (CMT/a ("cons" x ("nil")))) (term ("cons" x ("nil"))))

(test-equal 
 (term (CMT/a ("cons" (κ hole) ("nil"))))
 (term ("cons" ,TL-empty-cont ("nil"))))

;; Redexes
(test-equal (term (CMT/r (f x y))) (term (f x y)))
(test-equal 
 (term (CMT/r (f x (κ hole)))) 
 (term (f x ,TL-empty-cont)))

(test-equal (term (CMT/r (letrec ([(ref x) ("nil")]) z))) 
            (term (letrec ([(ref x) ("nil")]) z)))

(test-equal 
 (term (CMT/r (letrec ([(ref x) (κ hole)]) 
                (κ hole))))
 (term (letrec ([(ref x) ,TL-empty-cont])
         ,TL-empty-cont)))

(test-equal (term (CMT/r (call/cc f)))
            (term (f ((ref kont) (c-c-m [("square")])))))

(test-equal (term (CMT/r (match (κ hole) [("nil") (κ hole)]))) 
            (term (match ,TL-empty-cont
                    [("nil") ,TL-empty-cont])))

;; Contexts
(test-equal (term (CMT/T hole)) (term hole))

(test-equal (term (CMT/T ((ref f) (ref y) hole)))
            (term ((λ (x) ((ref f) (ref y) x))
                   (w-c-m ("square") (λ (x) ((ref f) (ref y) x))
                          hole))))

;; Compositions + Whole Programs
(test-equal
 (term (CMT ((ref f) (ref y) (call/cc (λ (k) (k z))))))
 (term
  ((λ (x) ((ref f) (ref y) x))
   (w-c-m ("square") (λ (x) ((ref f) (ref y) x))
          ((λ (k) (k z))
           ((ref kont) (c-c-m [("square")])))))))

;; Sub-units of big test
(test-equal (term (CMT ((ref +) ,(num 1) tmp)))
            (term ((ref +) ,(num 1) tmp)))

;;; Running the resulting programs
(define (CMT--> sl-version expected-ans)  
  (define tl-version
    (term (translate ,sl-version)))
  (test-TL-result
   (make-store [= ,=-impl] 
               [+ ,+-impl]
               [- ,--impl]
               [* ,*-impl]
               [if ,if-impl]) 
   ,tl-version
   ,expected-ans))

(CMT--> `(call/cc (λ (k) 
                    ((λ (tmp) ((ref +) ,(num 2) tmp))
                     (k ,(num 3)))))
        (num 3))
(CMT--> `((λ (tmp) ((ref +) ,(num 1) tmp))
          (call/cc (λ (k) 
                     ((λ (tmp) ((ref +) ,(num 2) tmp))
                      (k ,(num 3))))))
        (num 4))
