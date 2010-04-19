#lang scheme
(require redex
         "sl.ss"
         "tl.ss")

(define-extended-language sl-grammar+cmt
  sl-grammar
  [r (w ...)
     (letrec ([sigma w] ...) e)
     (case w l ...)
     (call/cc w)]
  [EE hole
      (v ... EE)])

(define-extended-language tl-grammar+cmt
  tl-grammar
  [r (w ...)
     (letrec ([sigma w] ...) e)
     (case w l ...)
     (w-c-m a e)
     (c-c-m)
     (abort e)]
  
  [EE (w-c-m v FF)
      FF]
  [FF hole
      (v v ... EE)])

(define tl:v? (redex-match tl-grammar v))
(define-metafunction sl-grammar+cmt
  CMT-v : v -> (side-condition any_1 (tl:v? (term any_1)))
  [(CMT-v (! sigma))
   (! sigma)]
  [(CMT-v (λ (x ...) e))
   (λ (x ...) (CMT-e e))]
  [(CMT-v (cont E))
   (λ (x) (abort ((! "resume") (get-marks (CMT-EE E)) x)))]
  [(CMT-v (K v ...))
   (K (CMT-v v) ...)])

(define tl:w? (redex-match tl-grammar w))
(define-metafunction sl-grammar+cmt
  CMT-w : w -> (side-condition any_1 (tl:w? (term any_1)))
  [(CMT-w x)
   x]
  [(CMT-w v)
   (CMT-v v)])

(define tl:a? (redex-match tl-grammar a))
(define-metafunction sl-grammar+cmt
  CMT-a : a -> (side-condition any_1 (tl:a? (term any_1)))
  [(CMT-a w)
   (CMT-w w)]
  [(CMT-a (K a ...))
   (K (CMT-a a) ...)])

(define tl:l? (redex-match tl-grammar l))
(define-metafunction sl-grammar+cmt
  CMT-l : l -> (side-condition any_1 (tl:l? (term any_1)))
  [(CMT-l [(K x ...) => e])
   [(K x ...) => (CMT-e e)]])

; XXX I don't like this contract, but tl:r doesn't work because of the call/cc case
(define tl:r? (redex-match tl-grammar+cmt r))
(define-metafunction sl-grammar+cmt
  CMT-r : r -> (side-condition any_1 (tl:e? (term any_1)))
  [(CMT-r (w ...))
   ((CMT-w w) ...)]
  [(CMT-r (letrec ([sigma w] ...) e))
   (letrec ([sigma (CMT-w w)] ...) (CMT-e e))]
  [(CMT-r (call/cc w))
   ((CMT-w w)
    ((λ (m)
       (λ (x) (abort ((! "resume") m x))))
     (c-c-m)))]
  [(CMT-r (case w l ...))
   (case (CMT-w w) (CMT-l l) ...)])

(define tl:EE? (redex-match tl-grammar+cmt EE))
(define-metafunction sl-grammar+cmt
  CMT-EE : EE -> (side-condition any_1 (tl:EE? (term any_1)))
  [(CMT-EE hole) 
   hole]
  [(CMT-EE (v ... EE))
   ,(local [(define x (variable-not-in (term (v ... EE)) 'x))
            (define k (term (λ (,x) ((CMT-v v) ... ,x))))]
      (term (,k (w-c-m ,k (CMT-EE EE)))))])

(define tl:e? (redex-match tl-grammar e))
(define-metafunction sl-grammar+cmt
  CMT-e : e -> (side-condition any_1 (tl:e? (term any_1)))
  [(CMT-e a_1)
   (CMT-a a_1)]
  [(CMT-e (in-hole EE_1 r_1))
   (in-hole (CMT-EE EE_1) (CMT-r r_1))])

(define resume-impl
  (term
   (λ (l v)
     (case l
       [("nil") => v]
       [("cons" k l) => (k (w-c-m k ((! "resume") l v)))]))))

(provide sl-grammar+cmt
         CMT-e
         CMT-EE
         CMT-r
         CMT-l
         CMT-a
         CMT-w
         CMT-v
         resume-impl)