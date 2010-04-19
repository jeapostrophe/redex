#lang scheme
(require redex
         redex/gui)

; SL

(define-language sl
  [e a
     (w ... e)
     (letrec ([sig v] ...) e)
     (call/cc w)
     (case w l ...)]
  [l ((K x ...) => e)]
  [a w
     (K a ...)]
  [w v
     x]
  [v (lambda (x ...) e)
     (K v ...)
     (kappa (hide-hole c))
     sig]
  [x (variable-except letrec call/cc case lambda kappa =>)]
  [K string]
  [sig (variable-prefix _)]
  [c (v ... c)
     hole]
  [sigma ()
         (sigma [sig v] ...)]
  [pair (/ sigma c)])

(define-metafunction sl
  [(sl-subst x v_x x)
   v_x]
  [(sl-subst x v_x x_ne)
   x_ne]
  [(sl-subst x v_x (w ... e))
   ((sl-subst x v_x w) ...
    (sl-subst x v_x e))]
  [(sl-subst x v_x (letrec ([sig v] ...) e))
   (letrec ([sig (sl-subset x v_x v)] ...)
     (sl-subst x v_x e))]
  [(sl-subst x v_x (call/cc w))
   (call/cc (sl-subst x v_x w))]
  [(sl-subst x v_x (case w l ...))
   (case (sl-subst x v_x w)
     (sl-subst x v_x l) ...)]
  [(sl-subst x v_x ((K x_k ...) => e))
   ((K x_k ...) => (sl-subst x v_x e))
   (side-condition (not (memq (term x) (term (x_k ...)))))]
  [(sl-subst x v_x ((K x_k ...) => e))
   ((K x_k ...) => e)]
  [(sl-subst x v_x (K a ...))
   (K (sl-subst x v_x a) ...)]
  [(sl-subst x v_x (lambda (x_i ...) e))
   (lambda (x_i ...) (sl-subst x v_x e))
   (side-condition (not (memq (term x) (term (x_i ...)))))]
  [(sl-subst x v_x (lambda (x_i ...) e))
   (lambda (x_i ...) e)])

(define-metafunction sl
  [(sl-subst* () () any) any]
  [(sl-subst* (x x_1 ...) (v v_1 ...) any)
   (sl-subst x v (sl-subst* (x_1 ...) (v_1 ...) any))])

(define-metafunction sl
  [(sl-lookup ([x v]) x)
   v]
  [(sl-lookup ([x_1 v_1] [x_2 v_2] ...) x_3)
   (sl-lookup ([x_2 v_2] ...) x_3)])

(define sl-reds
  (reduction-relation
   sl
   [--> (/ sigma (in-hole c_1 ((lambda (x ...) e) v ...)))
        (/ sigma (in-hole c_1 (sl-subst* (x ...)
                                         (v ...)
                                         e)))
        apply]
   [--> (/ sigma (in-hole c_1 (case (K v ...) 
                                any_1 ...
                                ((K x ...) => e)
                                any_2 ...)))
        (/ sigma (in-hole c_1 (sl-subst* (x ...)
                                         (v ...)
                                         e)))
        case]
   [--> (/ ([sig_1 v_1] ...) (in-hole c_1 (letrec ([sig v] ...) e)))
        (/ ([sig v] ... [sig_1 v_1] ...) (in-hole c_1 e))
        letrec]
   [--> (/ sigma (in-hole c_1 (sig v ...)))
        (/ sigma (in-hole c_1
                          ((sl-lookup sigma sig)
                           v ...)))
        sig-apply]
   [--> (/ sigma (in-hole c_1 (case sig l ...)))
        (/ sigma (in-hole c_1 (case (sl-lookup sigma sig) l ...)))
        sig-case]
   [--> (/ sigma (in-hole c_1 (call/cc v)))
        (/ sigma (in-hole c_1 (v (kappa c_1))))
        call/cc]
   [--> (/ sigma (in-hole c_1 ((kappa c_2) v)))
        (/ sigma (in-hole c_2 v))
        k-apply]
   ))

(test--> sl-reds
         (term (/ () ((lambda (x) x) (lambda (x y) (x y)))))
         (term (/ () (lambda (x y) (x y)))))

(test--> sl-reds
         (term (/ () (case ("K1" _1 _2)
                       [("K2" z) => z]
                       [("K1" x y) => x]
                       [("K4" x y z) => y])))
         (term (/ () _1)))

; TL

(define-language tl
  [e a
     (w ... e)
     (letrec ([sig v] ...) e)
     (w-c-m a e)
     (c-c-m)
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
  [x (variable-except letrec call/cc case lambda =>)]
  [K string]
  [sig (variable-prefix _)]
  [c (w-c-m v fc)
     fc]
  [fc (v ... c)
      hole]
  [sigma ([sig v] ...)]
  [pair (/ sigma c)])

(define-metafunction tl
  [(chi (v ... c)) (chi c)]
  [(chi (w-c-m v fc)) ("cons" v (chi fc))]
  [(chi any) ("nil")])

(define tl-reds
  (reduction-relation
   tl
   [--> (/ sigma (in-hole c_1 ((lambda (x ...) e) v ...)))
        (/ sigma (in-hole c_1 (sl-subst* (x ...)
                                         (v ...)
                                         e)))
        apply]
   [--> (/ sigma (in-hole c_1 (case (K v ...) 
                                any_1 ...
                                ((K x ...) => e)
                                any_2 ...)))
        (/ sigma (in-hole c_1 (sl-subst* (x ...)
                                         (v ...)
                                         e)))
        case]
   [--> (/ ([sig_1 v_1] ...) (in-hole c_1 (letrec ([sig v] ...) e)))
        (/ ([sig v] ... [sig_1 v_1] ...) (in-hole c_1 e))
        letrec]
   [--> (/ sigma (in-hole c_1 (sig v ...)))
        (/ sigma (in-hole c_1
                          ((sl-lookup sigma sig)
                           v ...)))
        sig-apply]   
   [--> (/ sigma (in-hole c_1 (case sig l ...)))
        (/ sigma (in-hole c_1 (case (sl-lookup sigma sig) l ...)))
        sig-case]
   [--> (/ sigma (in-hole c_1 (abort e)))
        (/ sigma e)
        abort]
   [--> (/ sigma (in-hole c_1 (w-c-m v_1 (w-c-m v_2 e))))
        (/ sigma (in-hole c_1 (w-c-m v_2 e)))
        #;(where c_1 (in-hole c_2 (v ... hole)))
        w-c-m-idempotent]
   [--> (/ sigma (in-hole c_1 (w-c-m v_1 v_2)))
        (/ sigma (in-hole c_1 v_2))
        #;(where c_1 (in-hole c_2 (v ... hole)))
        w-c-m-unwrap]
   [--> (/ sigma (in-hole c_1 (c-c-m)))
        (/ sigma (in-hole c_1 (chi c_1)))
        c-c-m]
   ))

(test--> tl-reds
         (term (/ () (c-c-m)))
         (term (/ () ("nil"))))

(test--> tl-reds
         (term (/ () (w-c-m _1 (w-c-m _2 (w-c-m _3 (c-c-m))))))
         (term (/ () ("cons" _3 ("nil")))))

(test--> tl-reds
         (term (/ () (w-c-m _1 (w-c-m _2 ((lambda (x) x) (w-c-m _3 (c-c-m)))))))
         (term (/ () ("cons" _2 ("cons" _3 ("nil"))))))

; SL -> TL

(define CMT/wv
  (term-match/single 
   sl
   ; Variables and values
   [x (term x)]
   [sig (term sig)]
   [(lambda (x ...) e)
    (term (lambda (x ...) ,(CMT (term e))))]
   [(kappa c)
    (term-let ([x (variable-not-in (term c) 'x)])
              (term (lambda (x)
                      (abort (_resume (chi ,(CMT/ctxt (term c))) x)))))]
   [(K a ...)
    (term (K ,@(map CMT (term (a ...)))))]))

(define CMT/redex
  (term-match/single 
   sl
   ; Redexes
   [(w ...)
    (term (,@(map CMT/wv (term (w ...)))))]
   [(letrec ([sig w] ...) e)
    (let* ([w-cmt (map CMT/wv (term (w ...)))]
           [ndef (map list (term (sig ...)) w-cmt)])
      (term (letrec ,ndef
              ,(CMT (term e)))))]
   [(call/cc w)
    (term (,(CMT/wv (term w))
           ((lambda (m)
              (lambda (x) (abort (_resume m x))))
            (c-c-m))))]
   [(case w l ...)
    (term (case ,(CMT/wv (term w))
            ,@(map CMT/redex (term (l ...)))))]
   [((K x ...) => e)
    (term ((K x ...) => ,(CMT (term e))))]))

(define-extended-language sl-with-r sl
  [r (w ...)
     (letrec ([sig w] ...) e)
     (call/cc w)
     (case w l ...)]
  [cr hole
      (v ... cr)])

(define CMT/ctxt
  (term-match/single 
   sl-with-r
   ; Contexts
   [(w ... cr)
    (term ((lambda (x) (,@(map CMT (term (w ...))) x))
           (w-c-m (lambda (x) (,@(map CMT (term (w ...))) x))
                  ,(CMT (term cr)))))]
   [hole (term hole)]
   ))

(define CMT/comp
  (term-match/single 
   sl-with-r
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
                    (c-c-m)))))

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
                   (w-c-m (lambda (x) (_1 _2 _3 x))
                          hole))))

(test-equal (CMT (term (_1 _2 (call/cc (lambda (k) (k _3))))))
            (term ((lambda (x) (_1 _2 x))
                   (w-c-m
                    (lambda (x) (_1 _2 x))
                    ((lambda (k) (k _3)) ((lambda (m) (lambda (x) (abort (_resume m x)))) (c-c-m)))))))

(define (with-resume t)
  (term (/ ()
           (letrec ([_resume
                     (lambda (l x)
                       (case l
                         [("nil") => x]
                         [("cons" v l) => (v (w-c-m v (_resume l x)))]))])
             ,t))))

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
                          (w-c-m v
                                 (_resume
                                  l
                                  x))))))])
                  ("3"))))

(test-results)