#lang scheme
(require redex
         "common.ss"
         "tl.ss"
         "cmt.ss")

; XXX Not exactly right, because shadowing is okay
(define (alpha-equal? t1 t2)
  (define t1->t2 (make-hasheq))
  (define inner-equal?
    (match-lambda*
      [(list (list-rest f1 r1)
             (list-rest f2 r2))
       (and (inner-equal? f1 f2)
            (inner-equal? r1 r2))]
      [(list (? symbol? s1)
             (? symbol? s2))
       (if (symbol=? s1 s2)
           #t
           (if (hash-has-key? t1->t2 s1)
               (local [(define s1-remap (hash-ref t1->t2 s1))]
                 (if (symbol=? s1-remap s2)
                     #t
                     (begin (printf "~S does not equal ~S~n" s1-remap s2)
                            #f)))
               (begin (hash-set! t1->t2 s1 s2)
                      (printf "Mapping ~S to ~S~n" s1 s2)
                      #t)))]
      [(list a1 a2)
       (equal? a1 a2)]))
  (inner-equal? t1 t2))

(require tests/eli-tester)
(test
 ;; Variables and Values
 (term (CMT-a z)) => (term z)
 (term (CMT-a (! "foo"))) => (term (! "foo"))
 (term (CMT-a (λ (x) z))) =>  (term (λ (x) z))
 
 (term (CMT-a (cont hole))) =>
 (term (λ (x) (abort ((! "resume") ("nil") x))))
 
 (term (CMT-a (cont ((! "f") (! "y") hole)))) =>
 (term (λ (x) (abort ((! "resume") ("cons" (λ (x) ((! "f") (! "y") x)) ("nil")) x))))
 
 (term (CMT-a ("nil"))) => (term ("nil"))
 (term (CMT-a ("cons" x ("nil")))) => (term ("cons" x ("nil")))
 
 (term (CMT-a ("cons" (cont hole) ("nil")))) =>
 (term ("cons" (λ (x) (abort ((! "resume") ("nil") x))) ("nil")))
 
 ;; Redexes
 (term (CMT-r (f x y))) => (term (f x y))
 
 (term (CMT-r (f x (cont hole)))) =>
 (term (f x (λ (x) (abort ((! "resume") ("nil") x)))))
 
 (term (CMT-r (letrec (["x" ("nil")]) z))) =>
 (term (letrec (["x" ("nil")]) z))
 
 (term (CMT-r (letrec (["x" (cont hole)]) 
                (cont hole))))
 => (term (letrec (["x" (λ (x) (abort ((! "resume") ("nil") x)))])
            (λ (x) (abort ((! "resume") ("nil") x)))))
 
 (term (CMT-r (call/cc f))) =>
 (term (f
        ((λ (m)
           (λ (x) (abort ((! "resume") m x))))
         (c-c-m))))
 
 (term (CMT-r (case (cont hole) [("nil") => (cont hole)]))) =>
 (term (case (λ (x) (abort ((! "resume") ("nil") x)))
         [("nil") => (λ (x) (abort ((! "resume") ("nil") x)))]))
 
 ;; Contexts
 (term (CMT-EE hole)) => (term hole)
 
 (term (CMT-EE ((! "f") (! "y") hole))) => 
 (term ((λ (x) ((! "f") (! "y") x))
        (w-c-m (λ (x) ((! "f") (! "y") x))
               hole)))
 
 ;; Compositions + Whole Programs
 (term (CMT-e ((! "f") (! "y") (call/cc (λ (k) (k z)))))) =>
 (term
  ((λ (x) ((! "f") (! "y") x))
   (w-c-m (λ (x) ((! "f") (! "y") x))
          ((λ (k) (k z))
           ((λ (m)
              (λ (x) (abort ((! "resume") m x))))
            (c-c-m))))))
 
 ;; Sub-units of big test
 (term (CMT-e ((! "+") ,(num 1) tmp))) =>
 (term ((! "+") ,(num 1) tmp)))

;;; Running the resulting programs
(define (CMT--> sl-version expected-ans)  
  (define tl-version
    (term (CMT-e ,sl-version)))  
  (test-->> -->_tl
            `(/ (snoc ,arith-store ["resume" -> ,resume-impl]) ,tl-version)
            `(/ (snoc ,arith-store ["resume" -> ,resume-impl]) ,expected-ans)))

(CMT--> `(call/cc (λ (k) 
                    ((λ (tmp) ((! "+") ,(num 2) tmp))
                     (k ,(num 3)))))
        (num 3))
(CMT--> `((λ (tmp) ((! "+") ,(num 1) tmp))
          (call/cc (λ (k) 
                     ((λ (tmp) ((! "+") ,(num 2) tmp))
                      (k ,(num 3))))))
        (num 4))

(test-results)