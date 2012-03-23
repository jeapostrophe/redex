#lang scheme
(require redex/reduction-semantics
         "set.ss")
(provide tl-grammar
         free-vars_tl
         -->_tl
         get-marks-tl
         wcm-merge
         wcm-replace)

;; Grammar
(define-language tl-grammar
  [e a
     (w ... e) 
     (letrec ([sigma v] ...) e)
     (match w l ...)
     (wcm ([w w] ...) e)
     (c-c-m w ...)
     (abort e)]
  [l [(K x ...) => e]
     [else => e]]
  [a w
     (K a ...)]
  [w v
     x]
  [v (! sigma) ; XXX not good
     (λ (x ...) e)
     (K v ...)]
  
  [x variable-not-otherwise-mentioned]
  [K string]
  [sigma string]
  
  [Sigma mt
         (snoc Sigma [sigma -> v])]
  [e* (/ Sigma e)]
  
  [E (wcm ([v v] ...) F)
     F]
  [F hole
     (v ... E)]
  [TE (/ Sigma E)])

;; Meta-functions
;;; Free vars
(define-metafunction tl-grammar
  defined-vars_tl : Sigma -> (sigma ...)
  [(defined-vars_tl mt) ()]
  [(defined-vars_tl (snoc Sigma_1 [sigma_1 -> v]))
   ,(cons (term sigma_1) (term (defined-vars_tl Sigma_1)))])
  
(define-metafunction tl-grammar
  free-vars_tl : any -> any
  ; e*
  [(free-vars_tl (/ Sigma_1 e_1))
   ,(set-sub (cons (term (free-vars_tl e_1))
                   (term (free-vars_tl Sigma_1)))
             (term (defined-vars_tl Sigma_1)))]
  ; Sigma
  [(free-vars_tl mt)
   ()]
  [(free-vars_tl (snoc Sigma_1 [sigma_1 -> v_1]))
   (sigma_1 (free-vars_tl Sigma_1)
            (free-vars_tl v_1))]
  ; e
  [(free-vars_tl (w_1 ... e_1))
   ((free-vars_tl w_1) ...
    (free-vars_tl e_1))]
  [(free-vars_tl (letrec ([sigma_1 v_1] ...) e_1))
   ,(set-sub (term ((free-vars_tl v_1) ... (free-vars_tl e_1)))
             (term (sigma_1 ...)))]
  [(free-vars_tl (match w_1 l_1 ...))
   ((free-vars_tl w_1) (free-vars_tl l_1) ...)]
  [(free-vars_tl (wcm ([w_k w_v] ...) e_1))
   ((free-vars_tl w_k) ...
    (free-vars_tl w_v) ...
    (free-vars_tl e_1))]
  [(free-vars_tl (c-c-m w_1 ...))
   ((free-vars_tl w_1) ...)]
  [(free-vars_tl (abort e_1))
   (free-vars_tl e_1)]
  ; l
  [(free-vars_tl [(K x_1 ...) => e_1])
   ,(set-sub (term (free-vars_tl e_1))
             (term (x_1 ...)))]
  [(free-vars_tl [else => e_1])
   (free-vars_tl e_1)]
  ; a/w/v
  [(free-vars_tl x_1) x_1]
  [(free-vars_tl (! sigma_1)) sigma_1]
  [(free-vars_tl (λ (x_1 ...) e_1))
   ,(set-sub (term (free-vars_tl e_1))
             (term (x_1 ...)))]
  [(free-vars_tl (K a_1 ...))
   ((free-vars_tl a_1) ...)])

;;; Substitution
(define-metafunction tl-grammar
  subst-e : x e e -> e
  [(subst-e x_s e_s a_1)
   (subst-a x_s e_s a_1)]
  [(subst-e x_s e_s (w_1 ... e_1))
   ((subst-w x_s e_s w_1) ...
    (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (letrec ([sigma_1 v_1] ...) e_1))
   (letrec ([sigma_1 (subst-v x_s e_s v_1)] ...)
     (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (wcm ([w_1 w_2]) e_1))
   (wcm ([(subst-a x_s e_s w_1)
            (subst-a x_s e_s w_2)])
          (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (c-c-m w_1 ...))
   (c-c-m (subst-a x_s e_s w_1) ...)]
  [(subst-e x_s e_s (abort e_1))
   (abort (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (match w_1 l_1 ...))
   (match (subst-w x_s e_s w_1)
     (subst-l x_s e_s l_1) ...)])

(define-metafunction tl-grammar
  subst-l : x e l -> l
  [(subst-l x_s e_s [(K x_1 ...) => e_1])
   [(K x_1 ...) => (subst-e x_s e_s e_1)]
   (side-condition (not (memq (term x_s) (term (x_1 ...)))))]
  [(subst-l x_s e_s l_1)
   l_1])

(define-metafunction tl-grammar
  subst-a : x e a -> e
  [(subst-a x_s e_s w_1)
   (subst-w x_s e_s w_1)]
  [(subst-a x_s e_s (K a_1 ...))
   (K (subst-a x_s e_s a_1) ...)])

(define-metafunction tl-grammar
  subst-w : x e w -> e
  [(subst-w x_s e_s v_1)
   (subst-v x_s e_s v_1)]
  [(subst-w x_s e_s x_s)
   e_s]
  [(subst-w x_s e_s x_1)
   x_1
   (side-condition (not (equal? (term x_s) (term x_1))))])

(define-metafunction tl-grammar
  subst-v : x e v -> e
  [(subst-v x_s e_s (λ (x_1 ...) e_1))
   (λ (x_1 ...) e_1)
   (side-condition (memq (term x_s) (term (x_1 ...))))]
  [(subst-v x_s e_s (λ (x_1 ...) e_1))
   ,(term-let ([(x_new ...) (variables-not-in (term e_s) (term (x_1 ...)))])
              (term (λ (x_new ...) 
                      (subst-e x_s e_s (subst-e* (x_1 ...) (x_new ...) e_1)))))
   (side-condition (not (memq (term x_s) (term (x_1 ...)))))]
  [(subst-v x_s e_s (K v_1 ...))
   (K (subst-v x_s e_s v_1) ...)]
  ;; All other values are atomic
  [(subst-v x_s e_s v_1)
   v_1])

(define-metafunction tl-grammar
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
(define-metafunction tl-grammar
  in-Sigma : Sigma sigma -> any
  [(in-Sigma mt sigma_1)
   (none)]
  [(in-Sigma (snoc Sigma_1 [sigma_1 -> v_1]) sigma_1)
   (some v_1)]
  [(in-Sigma (snoc Sigma_1 [sigma_1 -> v_1]) sigma_2)
   (in-Sigma Sigma_1 sigma_2)
   (side-condition (not (equal? (term sigma_1) (term sigma_2))))])

;;; Synthetic terms
(define-metafunction tl-grammar
  snoc* : Sigma ([sigma v] ...) -> Sigma
  [(snoc* Sigma_1 ())
   Sigma_1]
  [(snoc* Sigma_1 ([sigma_1 v_1] [sigma_2 v_2] ...))
   (snoc* (snoc Sigma_1 [sigma_1 -> v_1])
          ([sigma_2 v_2] ...))])

(define-metafunction tl-grammar
  select : v ([v v] ...) -> v
  [(select v_t ())
   ("none")]
  [(select v_t ([v_t v_vi] [v_k v_v] ...))
   ("some" v_vi)]
  [(select v_t ([v_ki v_vi] [v_k v_v] ...))
   (select v_t ([v_k v_v] ...))
   (side-condition (not (equal? (term v_t) (term v_ki))))])

(define-metafunction tl-grammar
  select* : (v ...) ([v v] ...) -> v
  [(select* (v_t ...) ([v_k v_v] ...))
   ("marks" (select v_t ([v_k v_v] ...))
            ...)])

(define (any-in?-fun l1 l2)
  (for/or ([i1 (in-list l1)])
    (for/or ([i2 (in-list l2)])
      (equal? i1 i2))))
(define-metafunction tl-grammar
  any-in? : (v ...) (v ...) -> any
  [(any-in? (v_1 ...) (v_2 ...))
   ,(any-in?-fun (term (v_1 ...)) (term (v_2 ...)))])

(define (->bool v)
  (not (not v)))
(define-metafunction tl-grammar
  ∈ : v (v ...) -> any
  [(∈ v_1 (v_2 ...))
   ,(->bool (member (term v_1) (term (v_2 ...))))])

(define-metafunction tl-grammar
  get-marks-tl : E (v ...) -> v
  [(get-marks-tl hole (v_t ...)) 
   ("nil")]
  [(get-marks-tl (v_1 ... E_1) (v_t ...))
   (get-marks-tl E_1 (v_t ...))]
  [(get-marks-tl (wcm ([v_k v_v] ...) F_1)
              (v_t ...))
   ("cons" 
    (select* (v_t ...) ([v_k v_v] ...))
    (get-marks-tl F_1 (v_t ...)))
   (side-condition (term (any-in? (v_t ...) (v_k ...))))]
  [(get-marks-tl (wcm ([v_k v_v] ...) F_1)
              (v_t ...))
   (get-marks-tl F_1 (v_t ...))
   (side-condition (term (¬ (any-in? (v_t ...) (v_k ...)))))])

(define-metafunction tl-grammar
  wcm-replace : v v ([v v] ...) -> ([v v] ...)
  ; Add it if it is not present
  [(wcm-replace v_k v_v ([v_ki v_vi] ...))
   ([v_k v_v] [v_ki v_vi] ...)
   (side-condition (term (¬ (∈ v_k (v_ki ...)))))]
  ; Replace if it is present
  [(wcm-replace v_k v_v ([v_kb v_vb] ...
                         [v_k v_v-old]
                         [v_ka v_va] ...))
   ([v_kb v_vb] ...
    [v_k v_v]
    [v_ka v_va] ...)])

(define-metafunction tl-grammar
  wcm-merge : ([v v] ...) ([v v] ...) -> ([v v] ...)
  [(wcm-merge ([v_k-fst v_v-fst] ...)
              ())
   ([v_k-fst v_v-fst] ...)]
  [(wcm-merge ([v_k-fst v_v-fst] ...)
              ([v_k v_v]
               [v_k-snd v_v-snd] ...))
   (wcm-merge any_step
              ([v_k-snd v_v-snd] ...))
   (where any_step (wcm-replace v_k v_v ([v_k-fst v_v-fst] ...)))])

;; Reduction rules
(define-metafunction tl-grammar
  ¬ : any -> any
  [(¬ #t) #f]
  [(¬ #f) #t])

(define-metafunction tl-grammar
  == : any any -> any
  [(== any_1 any_2)
   #t
   (side-condition (equal? (term any_1) (term any_2)))]
  [(== any_1 any_2)
   #f
   (side-condition (not (equal? (term any_1) (term any_2))))])

(define (no-blank-wcm?-fun t)
  (not (redex-match tl-grammar (in-hole E (wcm any hole)) t)))
(define-metafunction tl-grammar
  no-blank-wcm? : E -> any
  [(no-blank-wcm? E_1)
   ,(no-blank-wcm?-fun (term E_1))])

(define (not-adt?-fun t)
  (redex-match tl-grammar (λ (x ...) e) t))

(define-metafunction tl-grammar
  not-adt? : v -> any
  [(not-adt? v_1)
   ,(not-adt?-fun (term v_1))])

(define -->_tl
  (reduction-relation
   tl-grammar
   
   ; beta
   (~~> ((λ (x_1 ..._1) e_1) v_1 ..._1)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        "beta")
   ; beta on values
   (~~> ((K v_1 ...) v_2 ...)
        (abort ("not a function"))
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
   (~~> (match v_1)
        (abort ("match error"))
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
   
   ; abort
   (==> (in-hole E_1 (abort e_1))
        e_1
        "abort")
   
   ; wcm merge
   (==> (in-hole E_1 (wcm ([v_ki v_vi] ...)
                          (wcm ([v_kj v_vj] ...) e_1)))
        (in-hole E_1 (wcm (wcm-merge ([v_ki v_vi] ...)
                                     ([v_kj v_vj] ...))
                          e_1))
        (side-condition (term (no-blank-wcm? E_1)))
        "wcm merge")
   
   ; wcm return
   (==> (in-hole E_1 (wcm ([v_ki v_vi] ...) v_2))
        (in-hole E_1 v_2)
        (side-condition (term (no-blank-wcm? E_1)))
        "wcm return")
   
   ; c-c-m
   (==> (in-hole E_1 (c-c-m v_1 ...))
        (in-hole E_1 (get-marks-tl E_1 (v_1 ...)))
        "c-c-m")
   
   with
   ;; ==> is evaluation independent of store
   [(--> (/ Sigma_1 from)
         (/ Sigma_1 to))
    (==> from to)]
   ;; ~~> is evaluation in any E:
   [(==> (in-hole E_1 from)
         (in-hole E_1 to))
    (~~> from to)]))