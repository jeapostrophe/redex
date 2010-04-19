#lang scheme
(require redex
         "common.ss"
         "tl.ss"
         "cmt.ss")

(require tests/eli-tester)
(test
 ;; Variables and Values
 (term (CMT-a z)) => (term z)
 (term (CMT-a (! "foo"))) => (term (! "foo"))
 (term (CMT-a (λ (x) z))) =>  (term (λ (x) z))
 
 (term (CMT-a (cont hole))) =>
 (term (λ (x) (abort ((! "resume") ("nil") x))))
 
 (term (CMT-a (cont ((! "f") (! "y") hole)))) =>
 (term (λ (x) (abort ((! "resume") ("cons" ("marks" ("some" (λ (x) ((! "f") (! "y") x))) ("none")) ("nil")) x))))
 
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
         (c-c-m ("square") ("circle")))))
 
 (term (CMT-r (match (cont hole) [("nil") => (cont hole)]))) =>
 (term (match (λ (x) (abort ((! "resume") ("nil") x)))
         [("nil") => (λ (x) (abort ((! "resume") ("nil") x)))]))
 
 ;; Contexts
 (term (CMT-EE hole)) => (term hole)
 
 (term (CMT-EE ((! "f") (! "y") hole))) => 
 (term ((λ (x) ((! "f") (! "y") x))
        (wcm ([("square") (λ (x) ((! "f") (! "y") x))])
             hole)))
 
 ;; Compositions + Whole Programs
 (term (CMT-e ((! "f") (! "y") (call/cc (λ (k) (k z)))))) =>
 (term
  ((λ (x) ((! "f") (! "y") x))
   (wcm ([("square") (λ (x) ((! "f") (! "y") x))])
          ((λ (k) (k z))
           ((λ (m)
              (λ (x) (abort ((! "resume") m x))))
            (c-c-m ("square") ("circle")))))))
 
 ;; Sub-units of big test
 (term (CMT-e ((! "+") ,(num 1) tmp))) =>
 (term ((! "+") ,(num 1) tmp)))

;;; Running the resulting programs
(define (CMT--> sl-version expected-ans)  
  (define tl-version
    (term (CMT-e ,sl-version)))
  (define the-term
     `(/ (snoc ,arith-store ["resume" -> ,resume-impl]) ,tl-version))
  #;(traces -->_tl the-term)
  (test-->> -->_tl the-term
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

; XXX ccm tests

(test-results)