#lang scheme
(require redex
         "sl.ss"
         "tl.ss")

(define-extended-language sl-grammar+cmt
  sl-grammar
  [r (w ...)
     (letrec ([sigma w] ...) e)
     (match w l ...)
     (wcm ([a a]) e)
     (c-c-m a ...)
     (abort e)
     (call/cc w)]
  [EE hole
      (v ... EE)])

(define-extended-language tl-grammar+cmt
  tl-grammar
  [r (w ...)
     (letrec ([sigma w] ...) e)
     (match w l ...)
     (wcm ([a a]) e)
     (c-c-m a ...)
     (abort e)]
  
  [EE (wcm ([v v] ...) FF)
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
   (λ (x) (abort ((! "resume") (get-marks-tl (CMT-EE E) (("square") ("circle"))) x)))]
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
     (c-c-m ("square") ("circle"))))]
  [(CMT-r (match w l ...))
   (match (CMT-w w) (CMT-l l) ...)]
  [(CMT-r (wcm ([e_k e_v]) e_body))
   (wcm ([(CMT-e e_k)
          (CMT-e e_v)])
        (CMT-e e_body))]
  [(CMT-r (c-c-m a ...))
   (c-c-m (CMT-a a) ...)]
  [(CMT-r (abort e))
   (abort (CMT-e e))])

(define tl:EE? (redex-match tl-grammar+cmt EE))
(define-metafunction sl-grammar+cmt
  CMT-EE : EE -> (side-condition any_1 (tl:EE? (term any_1)))
  [(CMT-EE hole) 
   hole]
  ; XXX w-c-m
  [(CMT-EE (v ... EE))
   ,(local [(define x (variable-not-in (term (v ... EE)) 'x))
            (define k (term (λ (,x) ((CMT-v v) ... ,x))))]
      (term (,k (wcm ([("square") ,k]) (CMT-EE EE)))))])

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
     (match l
       [("nil") => v]
       [("cons" k*cm l) 
        => (match k*cm
             [("marks" mk mcm)
              => 
              ; XXX mcm
              (match mk
                [("some" k)
                 => (k (wcm ([("square") k]) ((! "resume") l v)))]
                [("none")
                 => ("error")])])]))))

(provide sl-grammar+cmt
         CMT-e
         CMT-EE
         CMT-r
         CMT-l
         CMT-a
         CMT-w
         CMT-v
         resume-impl)