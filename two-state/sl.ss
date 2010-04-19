#lang scheme
(require redex/reduction-semantics
         "set.ss")
(provide sl-grammar
         free-vars_sl
         -->_sl)

;; Grammar
(define-language sl-grammar
  [e a
     (w ... e) 
     (letrec ([sigma v] ...) e)
     (match w l ...)
     (call/cc w)]
  [l [(K x ...) => e]
     [else => e]]
  [a w
     (K a ...)]
  [w v
     x]
  [v (! sigma) ; XXX not good
     (λ (x ...) e)
     (unsafe-λ (x ...) e)
     (K v ...)
     (cont (hide-hole E))]
  
  [x variable-not-otherwise-mentioned]
  [K string]
  [sigma string]
  
  [Sigma mt
         (snoc Sigma [sigma -> v])]
  [e* (/ Sigma e)]
  
  [E hole
     (v ... E)]
  [TE (/ Sigma E)])

;; Meta-functions
;;; Free vars
(define-metafunction sl-grammar
  defined-vars_sl : Sigma -> (sigma ...)
  [(defined-vars_sl mt) ()]
  [(defined-vars_sl (snoc Sigma_1 [sigma_1 -> v]))
   ,(cons (term sigma_1) (term (defined-vars_sl Sigma_1)))])

(define-metafunction sl-grammar
  free-vars_sl : any -> any
  ; e*
  [(free-vars_sl (/ Sigma_1 e_1))
   ,(set-sub (cons (term (free-vars_sl e_1))
                   (term (free-vars_sl Sigma_1)))
             (term (defined-vars_sl Sigma_1)))]
  ; Sigma
  [(free-vars_sl mt)
   ()]
  [(free-vars_sl (snoc Sigma_1 [sigma_1 -> v_1]))
   (sigma_1 (free-vars_sl Sigma_1)
            (free-vars_sl v_1))]
  ; e
  [(free-vars_sl (w_1 ... e_1))
   ((free-vars_sl w_1) ...
    (free-vars_sl e_1))]
  [(free-vars_sl (letrec ([sigma_1 v_1] ...) e_1))
   ,(set-sub (term ((free-vars_sl v_1) ... (free-vars_sl e_1)))
             (term (sigma_1 ...)))]
  [(free-vars_sl (match w_1 l_1 ...))
   ((free-vars_sl w_1) (free-vars_sl l_1) ...)]
  [(free-vars_sl (call/cc w_1))
   (free-vars_sl w_1)]
  ; l
  [(free-vars_sl [(K x_1 ...) => e_1])
   ,(set-sub (term (free-vars_sl e_1))
             (term (x_1 ...)))]
  [(free-vars_sl [else => e_1])
   (free-vars_sl e_1)]
  ; a/w/v
  [(free-vars_sl x_1) x_1]
  [(free-vars_sl (! sigma_1)) sigma_1]
  [(free-vars_sl (λ (x_1 ...) e_1))
   ,(set-sub (term (free-vars_sl e_1))
             (term (x_1 ...)))]
  [(free-vars_sl (unsafe-λ (x_1 ...) e_1))
   ,(set-sub (term (free-vars_sl e_1))
             (term (x_1 ...)))]
  [(free-vars_sl (K a_1 ...))
   ((free-vars_sl a_1) ...)]
  [(free-vars_sl (cont E))
   (free-vars_sl E)]
  ; E
  [(free-vars_sl hole)
   ()]
  [(free-vars_sl (v_1 ... E_1))
   ((free-vars_sl v_1) ...
    (free-vars_sl E_1))])

;;; Substitution
(define-metafunction sl-grammar
  subst-e : x e e -> e
  [(subst-e x_s e_s a_1)
   (subst-a x_s e_s a_1)]
  [(subst-e x_s e_s (w_1 ... e_1))
   ((subst-w x_s e_s w_1) ...
    (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (letrec ([sigma_1 v_1] ...) e_1))
   (letrec ([sigma_1 (subst-v x_s e_s v_1)] ...)
     (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (call/cc w_1))
   (call/cc (subst-w x_s e_s w_1))]
  [(subst-e x_s e_s (match w_1 l_1 ...))
   (match (subst-w x_s e_s w_1)
     (subst-l x_s e_s l_1) ...)])

(define-metafunction sl-grammar
  subst-l : x e l -> l
  [(subst-l x_s e_s [(K x_1 ...) => e_1])
   [(K x_1 ...) => (subst-e x_s e_s e_1)]
   (side-condition (not (memq (term x_s) (term (x_1 ...)))))]
  [(subst-l x_s e_s [else => e_1])
   [else => (subst-e x_s e_s e_1)]]
  [(subst-l x_s e_s l_1)
   l_1])

(define-metafunction sl-grammar
  subst-a : x e a -> e
  [(subst-a x_s e_s w_1)
   (subst-w x_s e_s w_1)]
  [(subst-a x_s e_s (K a_1 ...))
   (K (subst-a x_s e_s a_1) ...)])

(define-metafunction sl-grammar
  subst-w : x e w -> e
  [(subst-w x_s e_s v_1)
   (subst-v x_s e_s v_1)]
  [(subst-w x_s e_s x_s)
   e_s]
  [(subst-w x_s e_s x_1)
   x_1
   (side-condition (not (equal? (term x_s) (term x_1))))])

(define-metafunction sl-grammar
  subst-v : x e v -> e
  [(subst-v x_s e_s (λ (x_1 ...) e_1))
   (λ (x_1 ...) e_1)
   (side-condition (memq (term x_s) (term (x_1 ...))))]
  [(subst-v x_s e_s (λ (x_1 ...) e_1))
   ,(term-let ([(x_new ...) (variables-not-in (term e_s) (term (x_1 ...)))])
              (term (λ (x_new ...) 
                      (subst-e x_s e_s (subst-e* (x_1 ...) (x_new ...) e_1)))))
   (side-condition (not (memq (term x_s) (term (x_1 ...)))))]
  [(subst-v x_s e_s (unsafe-λ (x_1 ...) e_1))
   (unsafe-λ (x_1 ...) e_1)
   (side-condition (memq (term x_s) (term (x_1 ...))))]
  [(subst-v x_s e_s (unsafe-λ (x_1 ...) e_1))
   ,(term-let ([(x_new ...) (variables-not-in (term e_s) (term (x_1 ...)))])
              (term (unsafe-λ (x_new ...) 
                              (subst-e x_s e_s (subst-e* (x_1 ...) (x_new ...) e_1)))))
   (side-condition (not (memq (term x_s) (term (x_1 ...)))))]
  [(subst-v x_s e_s (K v_1 ...))
   (K (subst-v x_s e_s v_1) ...)]
  ;; All other values are atomic
  [(subst-v x_s e_s v_1)
   v_1])

(define-metafunction sl-grammar
  ¬ : any -> any
  [(¬ #t) #f]
  [(¬ #f) #t])

(define-metafunction sl-grammar
  == : any any -> any
  [(== any_1 any_2)
   #t
   (side-condition (equal? (term any_1) (term any_2)))]
  [(== any_1 any_2)
   #f
   (side-condition (not (equal? (term any_1) (term any_2))))])

(define-metafunction sl-grammar
  subst-e* : (x ...) (e ...) e -> e
  [(subst-e* () () e_1)
   e_1]
  [(subst-e* (x_1 x_2 ...)
             (e_1 e_2 ...)
             e_t)
   (subst-e x_1 e_1
            (subst-e* (x_2 ...)
                      (e_2 ...)
                      e_t))])
;;; Lookup
(define-metafunction sl-grammar
  in-Sigma : Sigma sigma -> any
  [(in-Sigma mt sigma_1)
   (none)]
  [(in-Sigma (snoc Sigma_1 [sigma_1 -> v_1]) sigma_1)
   (some v_1)]
  [(in-Sigma (snoc Sigma_1 [sigma_1 -> v_1]) sigma_2)
   (in-Sigma Sigma_1 sigma_2)
   (side-condition (not (equal? (term sigma_1) (term sigma_2))))])

;;; Synthetic terms
(define-metafunction sl-grammar
  snoc* : Sigma ([sigma v] ...) -> Sigma
  [(snoc* Sigma_1 ())
   Sigma_1]
  [(snoc* Sigma_1 ([sigma_1 v_1] [sigma_2 v_2] ...))
   (snoc* (snoc Sigma_1 [sigma_1 -> v_1])
          ([sigma_2 v_2] ...))])

(define (not-adt?-fun t)
  (or (redex-match sl-grammar (λ (x ...) e) t)
      (redex-match sl-grammar (unsafe-λ (x ...) e) t)
      (redex-match sl-grammar (cont (hide-hole E)) t)))

(define-metafunction sl-grammar
  not-adt? : v -> any
  [(not-adt? v_1)
   #t
   (side-condition (not-adt?-fun (term v_1)))]
  [(not-adt? v_1)
   #f
   (side-condition (not (not-adt?-fun (term v_1))))])

;; Reduction rules
(define -->_sl
  (reduction-relation
   sl-grammar
   
   ; beta
   (~~> ((λ (x_1 ..._1) e_1) v_1 ..._1)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        "beta")
   ; beta (unsafe)
   (~~> ((unsafe-λ (x_1 ..._1) e_1) v_1 ..._1)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        "beta (unsafe)")
   ; beta on values
   (==> (in-hole E_1 ((K v_1 ...) v_2 ...))
        ("not a function")
        "no beta")
   
   ; match
   (~~> (match (K_1 v_1 ..._1) 
          [(K_1 x_1 ..._1) => e_1]
          l_1 ...)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        "match")
   ; match else
   (~~> (match v_1 [else => e_1] l_1 ...)
        e_1
        "match else")
   ; match empty
   (==> (in-hole E_1 (match v_1))
        ("match error")
        "match empty")
   ; match next
   (~~> (match (K_1 v_1 ...) 
          [(K_2 x_1 ...) => e_1]
          l_1 ...)
        (match (K_1 v_1 ...) l_1 ...)
        (side-condition (term (¬ (== K_1 K_2))))
        "match next")
   ; match next (other)
   (~~> (match v_1
          [(K_1 x_1 ...) => e_1]
          l_1 ...)
        (match v_1 l_1 ...)
        (side-condition (term (not-adt? v_1)))
        "match next (non-datatype)")
   
   ; letrec
   (--> (/ Sigma_1 (in-hole E_1 (letrec ([sigma_1 v_1] ...) e_1)))
        (/ (snoc* Sigma_1 ([sigma_1 v_1] ...)) (in-hole E_1 e_1))
        "letrec")
   
   ; sigma
   (--> (/ Sigma_1 (in-hole E_1 ((! sigma_1) v_1 ...)))
        (/ Sigma_1 (in-hole E_1 (v_l v_1 ...)))
        (where (some v_l) (in-Sigma Sigma_1 sigma_1))
        "sigma")
   
   ; match + sigma
   (--> (/ Sigma_1 (in-hole E_1 (match (! sigma_1) l_1 ...)))
        (/ Sigma_1 (in-hole E_1 (match v_1 l_1 ...)))
        (where (some v_1) (in-Sigma Sigma_1 sigma_1))
        "match + sigma")
   
   ; call/cc
   (==> (in-hole E_1 (call/cc v_1))
        (in-hole E_1 (v_1 (cont E_1)))
        "call/cc")
   
   ; cont invoke
   (==> (in-hole E_1 ((cont E_2) v_1))
        (in-hole E_2 v_1)
        "cont invoke")
   
   with
   ;; ==> is evaluation independent of store
   [(--> (/ Sigma_1 from)
         (/ Sigma_1 to))
    (==> from to)]
   ;; ~~> is evaluation in any E:
   [(==> (in-hole E_1 from)
         (in-hole E_1 to))
    (~~> from to)]))