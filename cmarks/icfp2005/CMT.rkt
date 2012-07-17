#lang racket

(require "SL-syntax.rkt"
         "SL-semantics.rkt"
         "TL-syntax.rkt"
         "../define-term.rkt"
         redex)

(provide CMT translate kont
         TL-equal? TL-reverse 
         map-set c-w-i-c-m
         restore-marks resume
         resume-marks frame-marks reverse-marks
         CMT/a CMT/r CMT/T)

(define-metafunction SL
  [(CMT a) (CMT/a a)]
  [(CMT (in-hole T r))
   (in-hole (CMT/T T) (CMT/r r))])

(define-metafunction SL
  [(CMT/a x) x]
  [(CMT/a σ) σ]
  [(CMT/a (λ (x ...) e))
   (λ (x ...) (CMT e))]
  [(CMT/a (κ E))
   (λ (x) (abort ((ref resume) v x)))
   (where v (resume-marks E))
   (where x ,(variable-not-in (term v) (term x)))]
  [(CMT/a (K a ...))
   (K (CMT/a a) ...)])

(define-metafunction SL
  [(CMT/r (a ...))
   ((CMT/a a) ...)]
  [(CMT/r (letrec ([σ w] ...) e))
   (letrec ([σ (CMT/a w)] ...) (CMT e))]
  [(CMT/r (match a l ...))
   (match (CMT/a a) (CMT/r l) ...)]
  [(CMT/r [(K x ...) e])
   [(K x ...) (CMT e)]]
  [(CMT/r (call/cc w))
   ((CMT/a w) ((ref kont) (c-c-m [("square")])))])

(define-metafunction SL
  [(CMT/T hole) hole]
  [(CMT/T (a ... T))
   (v_K (w-c-m ("square") v_K (CMT/T T)))
   (where (a_* ...) ((CMT/a a) ...))
   (where x ,(variable-not-in (term (a_* ...)) (term x)))
   (where v_K (λ (x) (a_* ... x)))])

(define-metafunction SL
  [(resume-marks E) 
   (resume-marks E #f ("nil"))]
  
  [(resume-marks hole k a_m)
   ("cons" (frame-marks k a_m) ("nil"))]
  [(resume-marks (a ... T) k a_m)
   ("cons" (frame-marks k a_m)
           (resume-marks T (λ (x) (a_* ... x)) ("nil")))
   (where (a_* ...) ((CMT a) ...))
   (where x ,(variable-not-in (term (a_* ...)) (term x)))])

(define-metafunction SL
  [(frame-marks #f a_m)
   ("nil")]
  [(frame-marks v_k a_m)
   ("cons" ("cons" ("cons" ("square") v_k)
                   ("nil")))])

(define-metafunction SL
  [(reverse-marks a)
   (reverse-marks a ("nil"))]
  [(reverse-marks ("nil") a) a]
  [(reverse-marks ("cons" a_1 a_2) a_3)
   (reverse-marks a_2 ("cons" a_1 a_3))])

(define-metafunction SL
  translate : e_1 -> (side-condition e_2 (TL-e? (term e_2)))
  [(translate e)
   (letrec ([(ref resume) ,resume]
            [(ref restore-marks) ,restore-marks]
            [(ref c-w-i-c-m) ,c-w-i-c-m]
            [(ref map-set) ,map-set]
            [(ref kont) ,kont]
            [(ref equal?) ,TL-equal?]
            [(ref reverse) ,TL-reverse])
     (CMT e))])
(define TL-e? (redex-match TL e))

(define-lw kont
  (term
   (λ (m)
     (λ (x)
       (abort ((ref resume) m x))))))

(define-lw c-w-i-c-m
  (term
   (λ (k proc default-v)
     ((λ (cms)
        ((λ (reversed)
           (proc
            (match reversed
              [("cons" _ rest)
               (match rest
                 [("cons" frame _)
                  (match frame
                    [("nil") default-v]
                    [("cons" mark _)
                     (match mark
                       [("cons" _ value) value])])])])))
         ((ref reverse) cms ("nil"))))
      (c-c-m [k])))))

(define-lw map-set
  (term
   (λ (map k v)
     (match map
       [("nil") ("cons" ("cons" k v) ("nil"))]
       [("cons" pair rest)
        (match pair
          [("cons" k’ v’)
           ((λ (eq)
              (match eq
                [("true")
                 ("cons" ("cons" k v) rest)]
                [("false")
                 ((λ (rest’) ("cons" pair rest’))
                  ((ref map-set) rest k v))]))
            ((ref equal?) k k’))])]))))

(define-lw restore-marks
  (term
   (λ (cms thnk)
     (match cms
       [("nil") (thnk)]
       [("cons" cm cms)
        (match cm
          [("cons" m v)
           (w-c-m m v
                  ((ref restore-marks) cms thnk))])]))))

(define-lw resume
  (term
   (λ (l v)
     (match l
       [("nil") v]
       [("cons" ms l)
        (match ms
          [("nil") ((ref resume) l v)]
          [("cons" m ms)
           (match m
             [("cons" j u)
              (match j
                [("square")
                 (match ms 
                   [("nil") 
                    (u (w-c-m ("square") u 
                              ((ref resume) l v)))]
                   ; How do you get a frame with both marks where square appears first?
                   ; All frames not introduced by "runtime" calls are marked first with
                   ; square (thus reported after any diamond mark), and `resume' seems
                   ; to restore this invariant. Use randomized testing to investigate.
                   [("cons" cms-mark _)
                    (match cms-mark
                      [("cons" _ cms)
                       (u (w-c-m ("square") u
                                 ((ref restore-marks) 
                                  cms
                                  (λ () 
                                    (w-c-m ("diamond") cms ((ref resume) l v))))))])])]
                [("diamond")
                 (match ms
                   [("nil")
                    ((ref restore-marks)
                     u
                     (λ () (w-c-m ("diamond") u ((ref resume) l v))))]
                   [("cons" kont-mark _)
                    (match kont-mark
                      [("cons" _ k)
                       (k (w-c-m ("square") k
                                 ((ref restore-marks)
                                  u
                                  (λ ()
                                    (w-c-m ("diamond") u ((ref resume) l v))))))])])])])])]))))

(define-lw TL-equal?
  (term
   (λ (x y)
     ((λ (cms)
        ((λ (reversed)
           (match reversed
             [("cons" frame _)
              (match frame
                [("cons" _ rest)
                 (match rest
                   [("nil") ("true")]
                   [("cons" _ __) ("false")])])]))
         ((ref reverse) cms ("nil"))))
      (w-c-m x ("")
             (w-c-m y ("")
                    (c-c-m [x y])))))))

(define-lw TL-reverse
  (term
   (λ (xs onto)
     (match xs
       [("nil") onto]
       [("cons" x xs’)
        ((ref reverse) xs’ ("cons" x onto))]))))
