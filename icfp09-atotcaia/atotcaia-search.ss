#lang scheme
(require redex
         tests/eli-tester)
(provide (all-defined-out))

; Figure 1
(define-language
  stlc
  [(t s) alpha
         B
         (var x) ; XXX New
         #;(x t) ; XXX New for poly
         (t → t)
         (t × t)]
  [sig (forall alphas t)]
  [e x
     (e : t)
     (⟨ t ⟩ e)
     ; λx:t.e
     (λ x : t e) 
     (e e)
     ; (e,e)
     (pair e e) 
     (proj i e)]
  [(c m) x
         (var x) ; XXX New
         (c ◦ c) ; XXX New
         ;(inst f ts) ; New for poly
         f
         ; λx:t.e
         (λ x : t m) 
         (m m)
         ; (m,m)
         (pair m m)
         (proj i m)]
  [Σ ·
     ; Σ, f : t1 → t2
     (Σ f : t → t)
     #;(Σ f : sig) ; New for poly
     ]
  [Γ ·
     ; Γ, x:t
     (Γ f : t)]
  [d b
     r
     s
     p
     q]
  [π mt
     (add π t)]
  [a ⊖
     ⊕]
  [subst ((alpha t) ...)]
  ; XXX New
  [eqs (equality any any)
       (lookup (Γ x) t)
       (type-check (Γ ⊢ m : t))
       (coerce (Σ Γ ⊢ d d e ~~> m : t))
       (generate (Σ ⊢ t <I d t ~~> c))
       (generate (Σ ⊢ π t <I r t ~~> c))
       (generate (Σ ⊢ π t <I p t ~~> c))
       (generate (Σ ⊢ π a t <I s t ~~> c))
       (generate (Σ ⊢ π a t <I q t ~~> c))
       (in (f : (t_0 → t_1) Σ))
       (in (f : sig Σ))]
  [ts (t ...)]
  [alphas (alpha ...)]
  [alpha (var x) ; XXX New
         x]
  [i 1
     2]
  [x variable-not-otherwise-mentioned]
  [f x
     (id t) ; XXX New
     (var x)] ; XXX New
  [B x])

(require (for-syntax scheme/list))
(define-for-syntax (syntax-split-at=> stx)
  (define (snoc l x)
    (append l (list x)))
  (let loop ([before empty]
             [l (syntax->list stx)])
    (if (empty? l)
        (values before empty)
        (syntax-case (first l) (=>)
          [=> (values before (rest l))]
          [_ (loop (snoc before (first l))
                   (rest l))]))))
(define-for-syntax (syntax-split-at=>* l)
  (for/lists (befores afters)
    ([s (in-list (syntax->list l))])
    (syntax-split-at=> s)))

(define-syntax (define-search-relation stx)
  (syntax-case stx ()
    [(define-search-relation lang
       (rr rel-name)
       [rule-name rule-body ...]
       ...)
     (let-values ([(befores afters) (syntax-split-at=>* #'((rule-body ...) ...))])
       (with-syntax
           ([((assumption ...) ...) befores]
            [(((name pat ...) extras ...) ...) afters])        
         (syntax/loc stx
           (begin
             #;(define-relation lang
                 [(rel-name pat ...) assumption ...]
                 ...)
             (define rr
               (reduction-relation
                lang
                [--> (env (any_0 (... ...))
                          (name pat ...)
                          any_after (... ...))
                     (env (any_0 (... ...))
                          assumption ...
                          any_after (... ...))
                     rule-name
                     extras ...]
                ...))))))]))

; XXX New
(define-metafunction
  stlc
  rewrite : x any any -> any
  [(rewrite x_0 any_0 (var x_0))
   any_0]
  [(rewrite x_!_0 any_0 (var (name x_0 x_!_0)))
   (var x_0)]
  [(rewrite x_0 any_0 (any_in ...))
   ((rewrite x_0 any_0 any_in)
    ...)]
  [(rewrite x_0 any_0 any_1)
   any_1])

(define (occurs? x e)
  (match e
    [`(var ,y)
     (if (eq? x y)
         #t
         #f)]
    [`(,e ...)
     (ormap (curry occurs? x) e)]
    [else
     #f]))

; XXX New
(define eq-rr
  (reduction-relation
   stlc
   [--> (env (any_var ...)
             (equality any_0 any_0)
             any_after ...)
        
        (env (any_var ...)
             any_after ...)
        "Eq-Id"]
   
   [--> (env (any_var ...)
             (equality (any_lf any_0 ..._0) (any_rf any_1 ..._0))
             any_after ...)
        
        (env (any_var ...)
             (equality any_lf any_rf)
             (equality any_0 any_1) ...
             any_after ...)
        "Eq-Split"
        (side-condition (not (equal? (term any_lf) 'var)))
        (side-condition (not (equal? (term any_rf) 'var)))]
   
   [--> (env (any_var ...)
             (equality any_0 (var x))
             any_after ...)
        
        (env (any_var ...)
             (equality (var x) any_0)
             any_after ...)
        "Eq-Sym"]
   
   [--> (env ([x_id any_val] ...)
             (equality (var x) any_0)
             any_after ...)
        
        (env ([x_id (rewrite x any_0 any_val)] ...
              [x any_0])
             (rewrite x any_0 any_after)
             ...)
        "Eq-Var"
        (side-condition (not (occurs? (term x) (term any_0))))]))

; XXX New
(define-search-relation
  stlc
  (maybe-eq-rr maybe-eq-rel)
  ["Maybe-Eq-Some"
   (equality t_0 t_1)
   =>
   (maybe-equality t_0 (some t_1))])

; XXX New
(define-search-relation
  stlc
  (in-rr in-rel)
  ["In-Head Sig"
   (equality f_1 f_2)
   (equality sig_0 sig_1)
   =>
   (in (f_1 : sig_0 (Σ f_2 : sig_1)))]
  ["In-Head"
   (equality f_1 f_2)
   (equality t_0 t_2)
   (equality t_1 t_3)
   =>
   (in (f_1 : (t_0 → t_1) (Σ f_2 : t_2 → t_3)))]
  ["In-Tail"   
   (in (f_0 : any_in Σ))
   =>
   (in (f_0 : any_in (Σ f_1 : t_2 → t_3)))])

(define-search-relation
  stlc
  (coerce-rr coerce-rel)
  ; Σ; Γ ⊢d,d′ e ~~> m : t
  ; coerce : (Σ Γ ⊢ d d e ~~> m : t)
  
  ; T-Var
  ["T-Var"   
   (equality x m)
   (lookup (Γ x) t)
   =>
   (coerce (Σ Γ ⊢ d d_prime x ~~> m : t))]
  
  ; T-As
  ["T-As"
   (coerce (Σ Γ ⊢ d d_prime e ~~> m : t))
   =>
   (coerce (Σ Γ ⊢ d d_prime (e : t) ~~> m : t))]
  
  ; T-Cast
  ["T-Cast (id)"
   (coerce (Σ Γ ⊢ d d_prime e ~~> m : (var t_prime)))
   (generate (Σ ⊢ (var t_prime) <I d_prime t ~~> (id t)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (⟨ t ⟩ e) ~~> m : t))
   (fresh t_prime)]
  
  ["T-Cast (coerce)"
   (equality m ((var c_n) (var m_n)))
   (coerce (Σ Γ ⊢ d d_prime e ~~> m : (var t_prime)))
   (generate (Σ ⊢ (var t_prime) <I d_prime t ~~> (var c_n)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (⟨ t ⟩ e) ~~> m : t))
   (fresh t_prime c_n m_n)]
  
  ; T-Abs
  ["T-Abs"
   (equality m (λ x : (var t_1) (var m_1)))
   (equality t ((var t_1) → (var t_prime)))
   (equality t_x (var t_1))
   (coerce (Σ (Γ x : t_x) ⊢ d d_prime e ~~> (var m_1) : (var t_prime)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (λ x : t_x e) ~~> m : t))
   (fresh t_prime m_1 t_1)]
  
  ; T-Pair
  ["T-Pair"   
   (equality t ((var t_1) × (var t_2)))
   (equality m (pair (var m_1) (var m_2)))
   (coerce (Σ Γ ⊢ d d_prime e_1 ~~> (var m_1) : t_1))
   (coerce (Σ Γ ⊢ d d_prime e_2 ~~> (var m_2) : t_2))
   =>
   (coerce (Σ Γ ⊢ d d_prime (pair e_1 e_2) ~~> m : t))
   (fresh m_1 m_2 t_1 t_2)]
  
  ; T-Proj
  ["T-Proj (1, id)"   
   (equality m_1 (proj 1 (var m)))
   (coerce (Σ Γ ⊢ d d_prime e ~~> (var m) : (var t)))
   (generate (Σ ⊢ (var t) <I d (t_1 × (var t_2)) ~~> (id (var t))))
   =>
   (coerce (Σ Γ ⊢ d d_prime (proj 1 e) ~~> m_1 : t_1))
   (fresh t t_2 m)]
  ["T-Proj (1, coerce)"   
   (equality m_1 (proj 1 ((var c) (var m))))
   (coerce (Σ Γ ⊢ d d_prime e ~~> (var m) : (var t)))
   (generate (Σ ⊢ (var t) <I d (t_1 × (var t_2)) ~~> (var c)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (proj 1 e) ~~> m_1 : t_1))
   (fresh t t_2 c m)]
  
  ["T-Proj (2, id)"   
   (equality m_1 (proj 2 (var m)))
   (coerce (Σ Γ ⊢ d d_prime e ~~> (var m) : (var t)))
   (generate (Σ ⊢ (var t) <I d ((var t_1) × t_2) ~~> (id (var t))))
   =>
   (coerce (Σ Γ ⊢ d d_prime (proj 2 e) ~~> m_1 : t_2))
   (fresh t t_1 m)]
  ["T-Proj (2, coerce)"   
   (equality m_1 (proj 2 ((var c) (var m))))
   (coerce (Σ Γ ⊢ d d_prime e ~~> (var m) : (var t)))
   (generate (Σ ⊢ (var t) <I d ((var t_1) × t_2) ~~> (var c)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (proj 2 e) ~~> m_1 : t_2))
   (fresh t t_1 c m)]
  
  ; T-App  
  ["T-App (id, id)"   
   (equality m ((var m_1) (var m_2)))
   (coerce (Σ Γ ⊢ d d_prime e_1 ~~> (var m_1) : (var t_1)))
   (generate (Σ ⊢ (var t_1) <I d ((var t_prime1) → t_prime2) ~~> (id (var t_1))))
   (coerce (Σ Γ ⊢ d d_prime e_2 ~~> (var m_2) : (var t_2)))
   (generate (Σ ⊢ (var t_2) <I d_prime (var t_prime1) ~~> (id (var t_2))))
   =>
   (coerce (Σ Γ ⊢ d d_prime (e_1 e_2) ~~> m : t_prime2))
   (fresh t_prime1 t_1 t_2 m_1 m_2)]
  ["T-App (id, coerce)"   
   (equality m ((var m_1) ((var c_prime) (var m_2))))
   (coerce (Σ Γ ⊢ d d_prime e_1 ~~> (var m_1) : (var t_1)))
   (generate (Σ ⊢ (var t_1) <I d ((var t_prime1) → t_prime2) ~~> (id (var t_1))))
   (coerce (Σ Γ ⊢ d d_prime e_2 ~~> (var m_2) : (var t_2)))
   (generate (Σ ⊢ (var t_2) <I d_prime (var t_prime1) ~~> (var c_prime)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (e_1 e_2) ~~> m : t_prime2))
   (fresh t_prime1 t_1 t_2 m_1 c_prime m_2)]
  
  ["T-App (coerce, id)"   
   (equality m (((var c) (var m_1)) (var m_2)))
   (coerce (Σ Γ ⊢ d d_prime e_1 ~~> (var m_1) : (var t_1)))
   (generate (Σ ⊢ (var t_1) <I d ((var t_prime1) → t_prime2) ~~> (var c)))
   (coerce (Σ Γ ⊢ d d_prime e_2 ~~> (var m_2) : (var t_2)))
   (generate (Σ ⊢ (var t_2) <I d_prime (var t_prime1) ~~> (id (var t_2))))
   =>
   (coerce (Σ Γ ⊢ d d_prime (e_1 e_2) ~~> m : t_prime2))
   (fresh t_prime1 t_1 t_2 c m_1 m_2)]
  ["T-App (coerce, coerce)"   
   (equality m (((var c) (var m_1)) ((var c_prime) (var m_2))))
   (coerce (Σ Γ ⊢ d d_prime e_1 ~~> (var m_1) : (var t_1)))
   (generate (Σ ⊢ (var t_1) <I d ((var t_prime1) → t_prime2) ~~> (var c)))
   (coerce (Σ Γ ⊢ d d_prime e_2 ~~> (var m_2) : (var t_2)))
   (generate (Σ ⊢ (var t_2) <I d_prime (var t_prime1) ~~> (var c_prime)))
   =>
   (coerce (Σ Γ ⊢ d d_prime (e_1 e_2) ~~> m : t_prime2))
   (fresh t_prime1 t_1 t_2 c m_1 c_prime m_2)]
  )

(define-search-relation
  stlc
  (generate-base-rr generate-base-rel)
  
  ; CB-Prim
  ["CB-Prim"   
   (in (f : (t → t_prime) Σ))
   =>
   (generate (Σ ⊢ t <I b t_prime ~~> f))]
  
  ; CB-Id
  ["CB-Id"   
   (equality f (id (var t_2)))
   (equality t_0 t_1)
   (equality t_0 (var t_2))
   =>
   (generate (Σ ⊢ t_0 <I b t_1 ~~> f))
   (fresh t_2)])

; XXX New
(define-search-relation
  stlc
  (l-rr l-rel)
  
  ["Lookup-Eq"
   (equality f_0 f_1)
   (equality t_0 t_1)
   =>
   (lookup ((Γ f_0 : t_0) f_1) t_1)]
  
  ["Lookup-Next"
   (lookup (Γ f_1) t_1)
   =>
   (lookup ((Γ f_0 : t_0) f_1) t_1)])

; XXX New
(define-metafunction
  stlc
  Γ/append : Σ Γ -> Γ
  [(Γ/append · Γ)
   Γ]
  [(Γ/append (Σ f : t_0 → t_1) Γ)
   (Γ/append Σ (Γ f : (t_0 → t_1)))])

(define-search-relation
  stlc
  (tc-rr tc-rel)
  ; Γ ⊢ m : t
  
  ; T-Var
  ["TC-Var"
   (lookup (Γ x) t)
   =>
   (type-check (Γ ⊢ x : t))]
  
  ; T-Abs
  ["TC-Abs"
   (type-check ((Γ x : t) ⊢ m : t_prime))
   =>
   (type-check (Γ ⊢ (λ x : t m) : (t → t_prime)))]
  
  ; T-Pair
  ["TC-Pair"   
   (type-check (Γ ⊢ m_1 : t_1))
   (type-check (Γ ⊢ m_2 : t_2))
   =>
   (type-check (Γ ⊢ (pair m_1 m_2) : (t_1 × t_2)))]
  
  ; T-Proj
  ["TC-Proj (1)"   
   (type-check (Γ ⊢ m : (t_1 × (var t_2))))
   =>
   (type-check (Γ ⊢ (proj 1 m) : t_1))
   (fresh t_2)]
  ["TC-Proj (2)"   
   (type-check (Γ ⊢ m : ((var t_1) × t_2)))
   =>
   (type-check (Γ ⊢ (proj 2 m) : t_2))
   (fresh t_1)]
  
  ; T-App 
  ["TC-App"   
   (equality (var t_1) ((var t_2) → t_3))
   (type-check (Γ ⊢ m_1 : (var t_1)))
   (type-check (Γ ⊢ m_2 : (var t_2)))
   =>
   (type-check (Γ ⊢ (m_1 m_2) : t_3))
   (fresh t_1 t_2)]
  )

(define-search-relation
  stlc
  (da-rr da-rel)
  ["DA-mt"
   (equality any_π (add mt t))
   =>
   (disjoint-add mt t any_π)]
  ["DA-id"
   (equality t_1 t_2)
   (equality any_π (add π t_1))
   =>
   (disjoint-add (add π t_1) t_2 any_π)]
  ["DA-nid"
   (disjoint-add π t_2 (var π2))
   (equality any_π (add (var π2) t_1))
   =>
   (disjoint-add (add π t_1) t_2 any_π)
   ; XXX Since this happens outside the logic, if there is a variable here then it will break.
   (side-condition (not (equal? (term t_1) (term t_2))))
   (fresh π2)])

; Figure 3, pg 332
(define-search-relation
  stlc
  (generate-trans-rr generate-trans-rel)
  
  ["CC-Id"   
   (equality c (id t))
   (equality t t_1)
   =>
   (generate (Σ ⊢ π t <I r t_1 ~~> c))]
  
  ["CC-PrimTrans"   
   (equality c_1 ((var c) ◦ (var f)))
   (in ((var f) : (t → (var t_primeprime)) Σ))
   (disjoint-add π (var t_primeprime) (var π1))
   (generate (Σ ⊢ (var π1) (var t_primeprime) <I r t_prime ~~> (var c)))
   =>
   (generate (Σ ⊢ π t <I r t_prime ~~> c_1))
   (fresh c f t_primeprime π1)]
  
  ["CC-InitPath"   
   (generate (Σ ⊢ (add mt t) t <I r t_prime ~~> c))
   =>
   (generate (Σ ⊢ t <I r t_prime ~~> c))])

; Figure 5, pg 335
(define-search-relation
  stlc
  (generate-struct-rr generate-struct-rel)
  
  ["CS-Init"
   (generate (Σ ⊢ (add mt t) ⊕ t <I s t_prime ~~> c))
   =>
   (generate (Σ ⊢ t <I s t_prime ~~> c))]
  
  ["CS-Id"
   (equality c (id t))
   (equality t t_prime)
   =>
   (generate (Σ ⊢ π a t <I s t_prime ~~> c))]
  
  ["CS-PrimTrans ⊕"
   (equality c_1 ((var c) ◦ (var f)))
   (in ((var f) : (t → (var t_1)) Σ))
   (disjoint-add π (var t_1) (var π1))
   (generate (Σ ⊢ (var π1) ⊖ (var t_1) <I s t_prime ~~> (var c)))
   =>
   (generate (Σ ⊢ π ⊕ t <I s t_prime ~~> c_1))
   (fresh c f t_1 π1)]
  ["CS-PrimTrans ⊖"
   (equality c_1 ((var c) ◦ (var f)))
   (in ((var f) : (t → (var t_1)) Σ))
   (disjoint-add π (var t_1) (var π1))
   (generate (Σ ⊢ (var π1) ⊕ (var t_1) <I s t_prime ~~> (var c)))
   =>
   (generate (Σ ⊢ π ⊖ t <I s t_prime ~~> c_1))
   (fresh c f t_1 π1)]
  
  ["CS-FunTrans"
   (equality t ((var t_1) → (var t_2)))
   (equality c_i ((var c_prime) ◦ (var c)))
   (generate (Σ ⊢ (var t_prime1) <I s (var t_1) ~~> (var c_1)))
   (generate (Σ ⊢ (var t_2) <I s (var t_prime2) ~~> (var c_2)))
   (equality c (λ f_n : ((var t_1) → (var t_2)) (λ x_n : (var t_prime1) ((var c_2) (f_n ((var c_1) x_n))))))
   (disjoint-add π ((var t_prime1) → (var t_prime2)) (var π1))
   (generate (Σ ⊢ π1 ⊖ ((var t_prime1) → (var t_prime2)) <I s t_prime ~~> (var c_prime)))
   =>
   (generate (Σ ⊢ π ⊕ t <I s t_prime ~~> c_i))
   (fresh f_n x_n t_1 t_2 c_prime c t_prime1 c_1 t_prime2 c_2 π1)]
  
  ["CS-PairTrans"
   (equality t ((var t_1) × (var t_2)))
   (equality c_i ((var c_prime) ◦ (var c)))
   (generate (Σ ⊢ (var t_1) <I s (var t_prime1) ~~> (var c_1)))
   (generate (Σ ⊢ (var t_2) <I s (var t_prime2) ~~> (var c_2)))
   (equality c 
             (λ x_n : ((var t_1) × (var t_2)) (pair ((var c_1) (proj 1 x_n))
                                                    ((var c_2) (proj 2 x_n)))))
   (disjoint-add π ((var t_prime1) → (var t_prime2)) (var π1))
   (generate (Σ ⊢ π1 ⊖ ((var t_prime1) × (var t_prime2)) <I s t_prime ~~> (var c_prime)))
   =>
   (generate (Σ ⊢ π ⊕ t <I s t_prime ~~> c_i))
   (fresh x_n t_1 t_2 c_prime c t_prime1 c_1 t_prime2 c_2 π1)])

; Figure 3 + 8, pg 332 + 337
#;(define-search-relation
  stlc
  (generate-polytrans-rr generate-polytrans-rel)
  
  ["CPQT-Id"   
   (equality c (id t))
   (equality t t_1)
   =>
   (generate (Σ ⊢ π t <I p t_1 ~~> c))]
  
  ; XXX add subst to language + rrs
  ; XXX Not in paper
  ["CPQT-PrimTrans 1"
   (equality c_1 ((var c) ◦ (inst (var f) ((var t_0)))))
   (in ((var f) : (forall ((var alpha_0)) ((var t_tau1) → (var t_tau2))) Σ))
   (subst (var alpha_0) (var t_0) t (var t_subst0))
   (equality (var t_tau1) (var t_subst0))
   (subst (var alpha_0) (var t_0) (var t_tau2) (var t_subst1))
   (equality (var t_2) (var t_subst1))
   (disjoint-add π (var t_2) (var π1))
   (disjoint-add (var π1) (var f) (var π2))
   (generate (Σ ⊢ (var π2) (var t_2) <I p t_prime ~~> (var c)))
   =>
   (generate (Σ ⊢ π t <I p t_prime ~~> c_1))
   (fresh c f t_tau1 t_tau2 π1 π2 alpha_0 t_0 t_subst0 t_subst1)]
  
  ["CPQT-InitPath"   
   (generate (Σ ⊢ (add mt t) t <I r t_prime ~~> c))
   =>
   (generate (Σ ⊢ t <I p t_prime ~~> c))])

(define all-rules
  (union-reduction-relations eq-rr
                             da-rr
                             maybe-eq-rr
                             tc-rr
                             coerce-rr
                             generate-base-rr
                             generate-trans-rr
                             generate-struct-rr
                             ;generate-polytrans-rr
                             in-rr
                             l-rr))

; Definitions

; XXX How to put Non-ambiguity definition into this framework? (pg 331)

; Definition 4. Strong non-ambiguity (pg 332)
(define (SNA Σ d d_prime)
  (redex-check* stlc
               (Γ e m_1 t_1 m_2 t_2)
               (implies (and (true? (term (coerce (,Σ Γ ⊢ ,d ,d_prime e ~~> m_1 : t_1))))
                             (true? (term (coerce (,Σ Γ ⊢ ,d ,d_prime e ~~> m_2 : t_2)))))
                        (and (equal? (term m_1) (term m_2))
                             (equal? (term t_1) (term t_2))))))

; Definition 5. Unique coercion paths
(define (NAC_π d Σ)
  (redex-check* stlc
               (t t_prime c c_prime)
               (implies (and (true? (term (generate (,Σ ⊢ t <I ,d t_prime ~~> c))))
                             (true? (term (generate (,Σ ⊢ t <I ,d t_prime ~~> c_prime)))))
                        (equal? (term c) (term c_prime)))))

; Definition 6. Unique Coercion to a Product Type
(define (NAC_× d Σ)
  (redex-check* stlc
               (t t_1 t_2 t_prime1 t_prime2 c c_prime)
               (implies (and (true? (term (generate (,Σ ⊢ t <I ,d (t_1 × t_2) ~~> c))))
                             (true? (term (generate (,Σ ⊢ t <I ,d (t_prime1 × t_prime2) ~~> c_prime)))))
                        (and (equal? (term t_1) (term t_prime1))
                             (equal? (term t_2) (term t_prime2))))))

; Definition 7. Unambiguous applications
(define (NAC_app d d_prime Σ)
  (redex-check* stlc
               (t_1 t_2 t_3 t_4 t_5 c_1 c_2 c_3 c_4)
               (implies (and (and (true? (term (generate (,Σ ⊢ t_1 <I ,d (t_3 → t_5) ~~> c_1))))
                                  (true? (term (generate (,Σ ⊢ t_2 <I ,d_prime t_3 ~~> c_3)))))
                             (and (true? (term (generate (,Σ ⊢ t_1 <I ,d (t_4 → t_6) ~~> c_2))))
                                  (true? (term (generate (,Σ ⊢ t_2 <I ,d_prime t_4 ~~> c_4))))))
                        (and (equal? (term t_3) (term t_4))
                             (equal? (term t_5) (term t_6))))))

(define (CoercionGraph Σ)
  (define g (make-hash))
  (define add-nodes!
    (term-match 
     stlc
     [· (void)]
     [(Σ f : t_1 → t_2)
      (begin
        (hash-update! g (term t_1) (curry list* (term t_2)) empty)
        (hash-ref! g (term t_2) empty)
        (add-nodes! (term Σ)))]))
  (add-nodes! Σ)
  g)

(define (graph-reachable g x y)
  (define visited (make-hash))
  (define (visit n)
    (cond
      [(equal? n y) #t]
      [(hash-has-key? visited n) #f]
      [else
       (hash-set! visited n #f)
       (for/or ([n (in-list (hash-ref g n empty))])
         (visit n))]))
  (visit x))

(define (Reachable Σ t1 t2)
  (graph-reachable (CoercionGraph Σ) t1 t2))

; Proposition 10 (pg 333)
(define (Abs/con-SNA n)
  (define Σ
    (for/fold ([Σ (term ·)])
      ([i (in-range n)])
      (define con_Xi (string->symbol (format "con_X~a" i)))
      (define abs_Xi (string->symbol (format "abs_X~a" i)))
      (define t_i (string->symbol (format "t~a" i)))
      (define X_i (string->symbol (format "X~a" i)))
      (term ((,Σ ,con_Xi : ,X_i → ,t_i) ,abs_Xi : ,t_i → ,X_i))))
  (SNA Σ (term r) (term r)))

; Theorem 11 (pg 335)
(define (BaseCoercions x)
  (match x
    ['·
     #t]
    [`(,Σ ,f : (,t0 → ,t1) → ,t2)
     #f]
    [`(,Σ ,f : ,t0 → ,t1)
     (BaseCoercions Σ)]))

; Figure 6 (pg 335)
(define (NAC^*_π s Σ)
  (match-define (list c_0 c_1 c_2 c_3 c_4 c_5 c_6)
                (for/list ([i (in-range 7)])
                  `(var ,(gensym 'c))))
  (redex-check* stlc
               ; XXX The paper does not define S or T
               (T t_1 t_2 t_prime1 t_prime2 t_0 t_prime0 S s_1 s_2 s_prime1 s_prime2)
               (implies
                (and (not (equal? (term (T t_1 t_2 t_prime1 t_prime2))
                                  (term (S s_1 s_2 s_prime1 s_prime2))))
                     ; These next three lines are expanded from what they wrote
                     (true? (term (generate (,Σ ⊢ t_0 <I r (T t_1 t_2) ~~> ,c_0))))
                     (true? (term (generate (,Σ ⊢ (T t_1 t_2) <I ,s (T t_prime1 t_prime2) ~~> ,c_1))))
                     (true? (term (generate (,Σ ⊢ (T t_prime1 t_prime2) <I r t_prime0 ~~> ,c_2))))
                     (false? (term (generate (,Σ ⊢ (T t_1 t_2) <I r (T t_prime1 t_prime2) ~~> ,c_3)))))
                (and (false? (term (generate (,Σ ⊢ t_0 <I r ~~> t_prime0))))
                     ; These next three lines are expanded from what they wrote
                     (true? (term (generate (,Σ ⊢ t_0 <I r (S s_1 s_2) ~~> ,c_4))))
                     (true? (term (generate (,Σ ⊢ (S s_1 s_2) <I ,s (S s_prime1 s_prime2) ~~> ,c_5))))
                     (true? (term (generate (,Σ ⊢ (S s_prime1 s_prime2) <I r t_prime0 ~~> ,c_6))))))))

; Definition 12 (pg 336)
(define (NAC_T d Σ)
  (redex-check* stlc
               ; XXX The paper does not define S or T
               (t_0 T t_1 t_2 S s_1 s_2 c_0 c_prime0)
               (implies (and (true? (term (generate (,Σ ⊢ t_0 <I ,d (T t_1 t_2) ~~> c_0))))
                             (true? (term (generate (,Σ ⊢ t_0 <I ,d (S s_1 s_2) ~~> c_prime0)))))
                        (and (equal? (term T) (term S))
                             (equal? (term t_1) (term s_1))
                             (equal? (term t_2) (term s_2))
                             (equal? (term c_0) (term c_prime0))))))

; Convenience
(define-syntax-rule (implies e1 e2)
  (if (eq? #t e1)
      e2
      #t))

(define-syntax-rule (equiv e1 e2)
  (bool-and (implies e1 e2)
            (implies e2 e1)))

(define-syntax-rule (bool-and e ...)
  (and (eq? #t e) ...))

(define (bool-not e)
  (not (eq? #t e)))

(define (search-relation-inject t)
  (term (env () ,t)))

(define (search-relation-results t)
  (apply-reduction-relation* all-rules (search-relation-inject t)))

(define (search-relation-successes t)
  (filter-map (match-lambda
                [`(env ([,x_id ,any_val] ...))
                 (for/hash ([id (in-list x_id)]
                            [val (in-list any_val)])
                   (values id val))]
                [_
                 #f])
              (search-relation-results t)))

(define (true? t)
  (cons? (search-relation-successes t)))

(define (false? t)
  (empty? (search-relation-successes t)))

(define (any l p?)
  (ormap p? l))

(define (trace-it t)
  (traces all-rules (search-relation-inject t)))

(define (step-it t)
  (stepper all-rules (search-relation-inject t)))

(define (redex-check-ans->bool a)
  (if (counterexample? a)
      (begin (printf "Counter example: ~S~n" a)
             #f)
      #t))

(define-syntax-rule (redex-check* lang for-all prop)
  (redex-check-ans->bool 
   (redex-check lang for-all prop
               #:attempts 1
               #:print? #f)))
