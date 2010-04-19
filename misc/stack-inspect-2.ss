#lang scheme
(require redex
         redex/gui)

(define-language tl
  [e a
     (w ... e)
     (letrec ([sig v] ...) e)
     (w-c-m ([a a] ...) e)
     (c-c-m (a ...))
     (abort e)
     (case w l ...)]
  [l ((K x ...) => e)]
  [a w
     (K a ...)]
  [w v
     x]
  [v (lambda (x ...) e)
     (K v ...)
     sig]
  [x (variable-except letrec case lambda => w-c-m c-c-m abort)]
  [K string]
  [sig (variable-prefix _)]
  [c (w-c-m ([v v] ...) fc)
     fc]
  [fc (v ... c)
      hole]
  [sigma ([sig v] ...)]
  [pair (/ sigma c)])

(define-extended-language tl-with-call/cc tl
  [e ....
     (call/cc w)]
  [v ....
     (kappa c)]
  [x (variable-except letrec call/cc case lambda => w-c-m c-c-m abort)])

(define-metafunction tl
  tl-subst/case : x v l -> l
  [(tl-subst/case x v_x ((K x_k ...) => e))
   ((K x_k ...) => (tl-subst x v_x e))
   (side-condition (not (memq (term x) (term (x_k ...)))))]
  [(tl-subst/case x v_x ((K x_k ...) => e))
   ((K x_k ...) => e)])

(define-metafunction tl-with-call/cc
  tl-subst : x v e -> e
  [(tl-subst x v_x x)
   v_x]
  [(tl-subst x v_x x_ne)
   x_ne]
  [(tl-subst x v_x (w ... e))
   ((tl-subst x v_x w) ...
    (tl-subst x v_x e))]
  [(tl-subst x v_x (letrec ([sig v] ...) e))
   (letrec ([sig (tl-subset x v_x v)] ...)
     (tl-subst x v_x e))]
  [(tl-subst x v_x (call/cc w))
   (call/cc (tl-subst x v_x w))]
  
  [(tl-subst x v_x (w-c-m ([a_k a_v] ...) e))
   (w-c-m ([a_k (tl-subst x v_x a_v)] ...)
          (tl-subst x v_x e))]
  [(tl-subst x v_x (c-c-m (a ...)))
   (c-c-m ((tl-subst x v_x a) ...))]
  [(tl-subst x v_x (abort e))
   (abort (tl-subst x v_x e))]
  
  [(tl-subst x v_x (case w l ...))
   (case (tl-subst x v_x w)
     (tl-subst/case x v_x l) ...)]
  [(tl-subst x v_x (K a ...))
   (K (tl-subst x v_x a) ...)]
  [(tl-subst x v_x (lambda (x_i ...) e))
   (lambda (x_i ...) (tl-subst x v_x e))
   (side-condition (not (memq (term x) (term (x_i ...)))))]
  [(tl-subst x v_x (lambda (x_i ...) e))
   (lambda (x_i ...) e)])

(define-metafunction tl-with-call/cc
  tl-subst* : (x ...) (v ...) e -> e
  [(tl-subst* () () any) any]
  [(tl-subst* (x x_1 ...) (v v_1 ...) any)
   (tl-subst x v (tl-subst* (x_1 ...) (v_1 ...) any))])

(define-metafunction tl-with-call/cc
  tl-lookup : ([x v] ...) x -> v
  [(tl-lookup ([x v_x] [x_2 v_2] ...) x)
   v_x]
  [(tl-lookup ([x_1 v_1] [x_2 v_2] ...) x_3)
   (tl-lookup ([x_2 v_2] ...) x_3)
   (side-condition (not (equal? (term x_1) (term x_3))))])

(define-metafunction tl-with-call/cc
  let : ([x e]) e -> (w e)
  [(let ([x e_1]) e_2)
   ((lambda (x) e_2) e_1)])

(define (chi-select/k k is)
  (if (empty? is)
      `("#f")
      (if (equal? k (first (first is)))
          (second (first is))
          (chi-select/k k (rest is)))))

(define (chi-select ks is)
  (if (empty? ks)
      empty
      (list* (chi-select/k (first ks) is)
             (chi-select (rest ks) is))))

(define-metafunction tl-with-call/cc
  chi : (v_k ...) c -> a
  [(chi (v_k ...) (v ... c))
   (chi (v_k ...) c)]
  [(chi (v_k1 ...) (w-c-m ([v_k2 v] ...) fc))
   ,(let-values ([(frame) (chi-select (term (v_k1 ...)) 
                                      (term ([v_k2 v] ...)))])
      (if (andmap (lambda (f) (equal? '("#f") f)) frame)
          (term (chi (v_k1 ...) fc))
          (term ("cons" ,@frame
                        (chi (v_k1 ...) fc)))))]
  [(chi (v_k ...) any) ("nil")])

(define tl-reds
  (reduction-relation
   tl-with-call/cc
   [--> (/ sigma (in-hole c_1 ((lambda (x ...) e) v ...)))
        (/ sigma (in-hole c_1 (tl-subst* (x ...)
                                         (v ...)
                                         e)))
        apply]
   [--> (/ sigma (in-hole c_1 (case (K v ...) 
                                any_1 ...
                                ((K x ...) => e)
                                any_2 ...)))
        (/ sigma (in-hole c_1 (tl-subst* (x ...)
                                         (v ...)
                                         e)))
        case]
   [--> (/ ([sig_1 v_1] ...) (in-hole c_1 (letrec ([sig v] ...) e)))
        (/ ([sig v] ... [sig_1 v_1] ...) (in-hole c_1 e))
        letrec]
   [--> (/ sigma (in-hole c_1 (sig v ...)))
        (/ sigma (in-hole c_1
                          ((tl-lookup sigma sig)
                           v ...)))
        sig-apply]   
   [--> (/ sigma (in-hole c_1 (case sig l ...)))
        (/ sigma (in-hole c_1 (case (tl-lookup sigma sig) l ...)))
        sig-case]
   [--> (/ sigma (in-hole c_1 (abort e)))
        (/ sigma e)
        abort]
   
   [--> (/ sigma (in-hole c_1 (w-c-m ([v_kb v_b] ... [v_k1 v_1] [v_ka v_a] ...)
                                     (w-c-m ([v_k1 v_2]) e))))
        (/ sigma (in-hole c_1 (w-c-m ([v_kb v_b] ... [v_k1 v_2] [v_ka v_a] ...)
                                     e)))
        w-c-m-idempotent]
   [--> (/ sigma (in-hole c_1 (w-c-m ([v_k1 v_1] ...)
                                     (w-c-m ([v_k2 v_2] ...) e))))
        (/ sigma (in-hole c_1 (w-c-m ([v_k1 v_1] ... [v_k2 v_2] ...) e)))
        w-c-m-commute
        (side-condition (not (ormap (lambda (k1)
                                      (member k1 (term (v_k2 ...))))
                                    (term (v_k1 ...)))))]
   [--> (/ sigma (in-hole c_1 (w-c-m ([v_k v_v] ...) v_2)))
        (/ sigma (in-hole c_1 v_2))
        w-c-m-unwrap]
   
   [--> (/ sigma (in-hole c_1 (c-c-m (v ...))))
        (/ sigma (in-hole c_1 (chi (v ...) c_1)))
        c-c-m]
   
   [--> (/ sigma (in-hole c_1 (call/cc v)))
        (/ sigma (in-hole c_1 (v (kappa c_1))))
        call/cc]
   [--> (/ sigma (in-hole c_1 ((kappa c_2) v)))
        (/ sigma (in-hole c_2 v))
        k-apply]
   
   ))

(test--> tl-reds
         (term (/ () ((lambda (x) x) (lambda (x y) (x y)))))
         (term (/ () (lambda (x y) (x y)))))

(test--> tl-reds
         (term (/ () (case ("K1" _1 _2)
                       [("K2" z) => z]
                       [("K1" x y) => x]
                       [("K4" x y z) => y])))
         (term (/ () _1)))

(test--> tl-reds
         (term (/ () (c-c-m (("square")))))
         (term (/ () ("nil"))))

(test--> tl-reds
         (term (/ () (w-c-m ([("square") _1 ])
                            (w-c-m ([("square") _2])
                                   (w-c-m ([("square") _3])
                                          (c-c-m (("square"))))))))
         (term (/ () ("cons" _3 ("nil")))))

(test--> tl-reds
         (term (/ () (w-c-m ([("square") _1])
                            (w-c-m ([("square") _2])
                                   ((lambda (x) x) (w-c-m ([("square") _3])
                                                          (c-c-m (("square")))))))))
         (term (/ () ("cons" _2 ("cons" _3 ("nil"))))))

; CMT : Continuation Mark Transformation
(define CMT/wv
  (term-match/single 
   tl-with-call/cc
   ; Variables and values
   [x (term x)]
   [sig (term sig)]
   [(lambda (x ...) e)
    (term (lambda (x ...) ,(CMT (term e))))]
   [(kappa c)
    (term-let ([x (variable-not-in (term c) 'x)])
              (term (lambda (x)
                      (abort (_resume (chi (("square")) ,(CMT/ctxt (term c))) x)))))]
   [(K a ...)
    (term (K ,@(map CMT (term (a ...)))))]))

(define CMT/redex
  (term-match/single 
   tl-with-call/cc
   ; Redexes
   [(w ...)
    (term (,@(map CMT (term (w ...)))))]
   [(w ... e)
    (term ((lambda (x) (,@(map CMT (term (w ...))) x))
           (w-c-m ([("square") (lambda (x) (,@(map CMT (term (w ...))) x))])
                  ,(CMT (term e)))))]
   [(letrec ([sig w] ...) e)
    (let* ([w-cmt (map CMT/wv (term (w ...)))]
           [ndef (map list (term (sig ...)) w-cmt)])
      (term (letrec ,ndef
              ,(CMT (term e)))))]
   [(call/cc w)
    (term (,(CMT/wv (term w))
           ((lambda (m)
              (lambda (x) (abort (_resume m x))))
            (c-c-m (("square") ("diamond"))))))]
   ; This is wrong because of a test below...
   [(w-c-m ([a_k a] ...) e)
    (term (w-c-m ([a_k a] ...)
                 (w-c-m ([("diamond") ("list" ("pair" a_k a) ...)])
                        ,(CMT (term e)))))]
   [(c-c-m (a ...))
    (term (c-c-m (a ...)))]
   
   [(case w l ...)
    (term (case ,(CMT/wv (term w))
            ,@(map CMT/redex (term (l ...)))))]
   [((K x ...) => e)
    (term ((K x ...) => ,(CMT (term e))))]))

(define-extended-language tl-with-r tl-with-call/cc
  [r (w ...)
     (letrec ([sig w] ...) e)
     (call/cc w)
     (case w l ...)]
  [cr hole
      (v ... cr)])

(define CMT/ctxt
  (term-match/single 
   tl-with-r
   ; Contexts
   [(w ... cr)
    (term ((lambda (x) (,@(map CMT (term (w ...))) x))
           (w-c-m ([("square") (lambda (x) (,@(map CMT (term (w ...))) x))])
                  ,(CMT (term cr)))))]
   [hole (term hole)]
   ))

(define CMT/comp
  (term-match/single 
   tl-with-r
   ; Compositions
   [(in-hole cr r)
    (plug (CMT (term cr)) (CMT (term r)))]
   ))

(define (CMT t)
  #;(printf "~S~n" `(cmt ,t))
  (let/ec esc
    (for-each (lambda (f)
                (with-handlers ([exn:fail? void
                                      #;(lambda (e) ((error-display-handler) (exn-message e) e))])
                  (esc (f t))))
              (list CMT/wv CMT/redex CMT/ctxt CMT/comp))
    #f))

(test-equal (CMT (term x))
            (term x))
(test-equal (CMT (term _id))
            (term _id))
(test-equal (CMT (term (lambda (x y) _2)))
            (term (lambda (x y) _2)))
(test-equal (CMT (term (kappa hole)))
            (term (lambda (x) (abort (_resume ("nil") x)))))
(test-equal (CMT (term (kappa (_1 _2 _3 hole))))
            (term (lambda (x) (abort (_resume ("cons" (lambda (x) (_1 _2 _3 x)) ("nil")) x)))))
(test-equal (CMT (term ("list" _1 _2 _3)))
            (term ("list" _1 _2 _3)))

(test-equal (CMT (term (call/cc (lambda (x) x))))
            (term ((lambda (x) x)
                   ((lambda (m) (lambda (x) (abort (_resume m x))))
                    (c-c-m (("square")))))))

(test-equal (CMT (term (letrec ([_1 (lambda (x y) y)]) _1)))
            (term (letrec ([_1 (lambda (x y) y)]) _1)))

(test-equal (CMT (term (case ("list" _1 _2 _3)
                         [("list" x y z) => x])))
            (term (case ("list" _1 _2 _3)
                    [("list" x y z) => x])))

(test-equal (CMT (term hole))
            (term hole))
(test-equal (CMT (term (_1 _2 _3 hole)))
            (term ((lambda (x) (_1 _2 _3 x))
                   (w-c-m ([("square") (lambda (x) (_1 _2 _3 x))])
                          hole))))

(test-equal (CMT (term (_1 _2 (call/cc (lambda (k) (k _3))))))
            (term ((lambda (x) (_1 _2 x))
                   (w-c-m ([("square") (lambda (x) (_1 _2 x))])
                          ((lambda (k) (k _3))
                           ((lambda (m) (lambda (x) (abort (_resume m x))))
                            (c-c-m (("square")))))))))

(define (with-resume t)
  (term (/ ()
           (letrec ([_resume
                     (lambda (l x)
                       (case l
                         [("nil") => x]
                         [("cons" v l) => (v (w-c-m ([("square") v]) (_resume l x)))]))])
             ,t))))

#;(traces tl-reds 
          (with-resume 
           (CMT 
            (term
             (letrec ([_1 (lambda (x y) y)]
                      [_2 ("2")]
                      [_3 ("3")])
               (_1 _2 (call/cc (lambda (k) (k _3)))))))))

(test--> tl-reds 
         (with-resume 
          (CMT 
           (term
            (letrec ([_1 (lambda (x y) y)]
                     [_2 ("2")]
                     [_3 ("3")])
              (_1 _2 (call/cc (lambda (k) (k _3))))))))
         (term (/ ([_1 (lambda (x y) y)]
                   [_2 ("2")]
                   [_3 ("3")]
                   [_resume
                    (lambda (l x)
                      (case l
                        (("nil") => x)
                        (("cons" v l)
                         =>
                         (v
                          (w-c-m ([("square") v])
                                 (_resume l x))))))])
                  _3)))

(test--> tl-reds 
         (with-resume 
          (CMT 
           (term
            (letrec ([_1 (lambda (x y) y)]
                     [_2 ("2")]
                     [_3 ("3")])
              (w-c-m ([("k1") _1])
                     (_1 _2 (call/cc (lambda (k) (k (c-c-m (("k1"))))))))))))
         (term
          (/
           ((_1 (lambda (x y) y))
            (_2 ("2"))
            (_3 ("3"))
            (_resume
             (lambda (l x)
               (case l
                 (("nil") => x)
                 (("cons" v l)
                  =>
                  (v
                   (w-c-m
                    ((("square") v))
                    (_resume
                     l
                     x))))))))
           ("cons" _1 ("nil")))))

(traces tl-reds 
        (with-resume 
         (CMT 
          (term
           (letrec ([_1 (lambda (x y) y)]
                    [_2 ("2")]
                    [_3 ("3")])
             (w-c-m ([("k1") _1])
                    (_1 _2 (call/cc (lambda (k) (k (c-c-m (("k1")))))))))))))

(test-results)