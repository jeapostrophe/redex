#lang racket
(require redex/reduction-semantics
         "../define-term.rkt"
         "common.rkt"
         "sl.rkt"
         "tl.rkt")

(define-extended-language sl-grammar+cmt
  sl-grammar
  [r (w ... a)
     (letrec ([sigma w] ...) e)
     (match w l ...)
     (call/cc w)]
  
  [EE hole
      (w ... EE)])

(define-extended-language tl-grammar+cmt
  tl-grammar
  [r (w ...)
     (letrec ([sigma w] ...) e)
     (match w l ...)
     (wcm ([a a] ...) e)
     (c-c-m a ...)
     (abort e)]
  
  [EE (wcm ([v v] ...) FF)
      FF]
  [FF hole
      (v ... EE)])

(define-metafunction sl-grammar
  sl-context->marks : E -> (side-condition any_1 (tl:v? (term any_1)))
  [(sl-context->marks hole)
   ("nil")]
  [(sl-context->marks (v ... E))
   ,(term-let ([x (term (fresh-id (v ... E)))])
              (term ("cons" 
                     ("marks" 
                      ("some" (λ (x) ((CMT-v v) ... x))))
                     (sl-context->marks E))))])

(define tl:v? (redex-match tl-grammar v))
(define-metafunction sl-grammar+cmt
  CMT-v : v -> (side-condition any_1 (tl:v? (term any_1)))
  [(CMT-v (cont E_1))
   (λ (x) 
     (abort ((! "resume") 
             (sl-context->marks E_1)
             x)))]
  [(CMT-v (λ (x ...) e))
   (λ (x ...) 
     (wcm ([("safe-call?") ("#t")])
          (CMT-e e)))]
  [(CMT-v (unsafe-λ (x ...) e))
   (λ (x ...) e)]
  [(CMT-v (! sigma))
   (! sigma)]
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
   [(K x ...) => (CMT-e e)]]
  [(CMT-l [else => e])
   [else => (CMT-e e)]])

(define tl:r? (redex-match tl-grammar+cmt r))
(define-metafunction sl-grammar+cmt
  CMT-r : r -> (side-condition any_1 (tl:r? (term any_1)))
  [(CMT-r (w ... a))
   (wcm ([("safe-call?") ("#f")])
        ((CMT-w w) ... (CMT-a a)))]
  [(CMT-r (letrec ([sigma w] ...) e))
   (letrec ([sigma (CMT-w w)] ...) (CMT-e e))]
  [(CMT-r (call/cc w))
   ((! "call/cc") (CMT-w w))]
  [(CMT-r (match w l ...))
   (match (CMT-w w) (CMT-l l) ...)])

(define tl:EE? (redex-match tl-grammar+cmt EE))
(define-metafunction sl-grammar+cmt
  fresh-id : (any ...) -> x
  [(fresh-id (any_1 ...))
   ,(variable-not-in (term (any_1 ...)) 'x)])

(define-metafunction sl-grammar+cmt
  CMT-EE : EE -> (side-condition any_1 (tl:EE? (term any_1)))
  [(CMT-EE hole) 
   hole]
  #;[(CMT-EE (w ... EE))
     (expr_k (wcm ([("square") expr_k]) (CMT-EE EE)))
     (where expr_k (λ (x) ((CMT-w w) ... x)))
     (fresh x)]
  #;[(CMT-EE (w ... EE))
     (k (wcm ([("square") k]) (CMT-EE EE)))
     #;(where x ,(variable-not-in (term (w ... EE)) 'x))
     #;(where k (λ (x) ((CMT-w w) ... x)))]
  [(CMT-EE (w ... EE))
   ,(term-let ([x (term (fresh-id (w ...)))]
               [k (term (λ (x) ((CMT-w w) ... x)))])
              (term (k (wcm ([("square") k]) (CMT-EE EE)))))])

(define tl:e? (redex-match tl-grammar e))
(define-metafunction sl-grammar+cmt
  CMT-e : e -> (side-condition any_1 (tl:e? (term any_1)))
  [(CMT-e a_1)
   (CMT-a a_1)]
  [(CMT-e (in-hole EE_1 r_1))
   (in-hole (CMT-EE EE_1) (CMT-r r_1))])

(define-metafunction sl-grammar+cmt
  CMT-top : e -> (side-condition any_1 (tl:e? (term any_1)))
  [(CMT-top e_1)
   (CMT-e e_1)])

(define-lw resume-impl
  (term
   (λ (l v)
     (match l
       [("nil") => v]
       [("cons" k*cm l) 
        => (match k*cm
             [("marks" mk)
              =>
              (match mk
                [("some" k)
                 => (k (wcm ([("square") k]) ((! "resume") l v)))]
                [("none")
                 => (abort ("not marks"))])])]))))

(define-lw callcc-impl
  (term
   (λ (f)
     ((λ (k)
        (f k))
      ((λ (m)
         (λ (x) (abort ((! "resume") m x))))
       (c-c-m ("square")))))))
(define-lw safe-callcc-impl
  (term
   (λ (f)
     ((λ (is-safe?)
        (match is-safe?
          [("#t") =>
                  ((λ (k)
                     (f k))
                   ((λ (m)
                      (λ (x) (abort ((! "resume") m x))))
                    (c-c-m ("square"))))]
          [("#f") => (abort ("unsafe context"))]))
      ((! "all-safe?")
       (c-c-m ("safe-call?")))))))

(define (CMT sl-version mode)
  (define the-callcc
    (case mode
      [(unsafe) callcc-impl]
      [(safe) safe-callcc-impl]))
  (define tl-version
    (term (letrec (["resume" ,resume-impl]
                   ["call/cc" ,the-callcc])
            (CMT-top ,(with-safe sl-version)))))
  tl-version)

(provide sl-grammar+cmt
         tl-grammar+cmt
         sl-context->marks
         CMT
         CMT-top
         CMT-e
         CMT-EE
         CMT-r
         CMT-l
         CMT-a
         CMT-w
         CMT-v
         resume-impl
         callcc-impl
         safe-callcc-impl)
