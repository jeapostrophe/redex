#lang scheme
(require redex)
(provide tl-grammar
         -->_tl
         get-marks-tl)

;; Grammar
(define-language tl-grammar
  [e a
     (w w ... e) 
     (letrec ([sigma v] ...) e)
     (match w l ...)
     (wcm ([a a]) e)
     (c-c-m a ...)
     (abort e)]
  [l [(K x ...) => e]]
  [a w
     (K a ...)]
  [w v
     x]
  [v (λ (x ...) e)
     (K v ...)
     (! sigma)]
  
  [x variable-not-otherwise-mentioned]
  [K string]
  [sigma string]
  
  [E (wcm ([v v] ...) F)
     F]
  [F hole
     (v v ... E)]
  [Sigma mt
         (snoc Sigma [sigma -> v])]
  [TE (/ Sigma E)])

;; Meta-functions
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
  [(subst-e x_s e_s (wcm ([a_1 a_2]) e_1))
   (wcm ([(subst-a x_s e_s a_1)
            (subst-a x_s e_s a_2)])
          (subst-e x_s e_s e_1))]
  [(subst-e x_s e_s (c-c-m a_1 ...))
   (c-c-m (subst-a x_s e_s a_1) ...)]
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
  in-match : (K v ...) (l ...) -> l
  [(in-match (K_1 v_1 ...)
             ([(K_1 x_1 ...) => e_1] l_2 ...))
   [(K_1 x_1 ...) => e_1]
   (side-condition (= (length (term (v_1 ...)))
                      (length (term (x_1 ...)))))]
  [(in-match (K_1 v_1 ...)
             ([(K_2 x_1 ...) => e_1] l_2 ...))
   (in-match (K_1 v_1 ...)
             (l_2 ...))
   (side-condition (not (and (equal? (term K_1) (term K_2))
                             (= (length (term (v_1 ...)))
                                (length (term (x_1 ...)))))))])

(define-metafunction tl-grammar
  in-Sigma : Sigma sigma -> v
  [(in-Sigma (snoc Sigma_1 [sigma_1 -> v_1]) sigma_1)
   v_1]
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

(define-metafunction tl-grammar
  get-marks-tl : E (v ...) -> v
  [(get-marks-tl hole (v_t ...)) 
   ("nil")]
  [(get-marks-tl (v_1 ... E_1) (v_t ...))
   (get-marks-tl E_1 (v_t ...))]
  [(get-marks-tl (wcm ([v_k v_v] ...) F_1)
              (v_t ...))
   ("cons" (select* (v_t ...) ([v_k v_v] ...))
           (get-marks-tl F_1 (v_t ...)))])

(define-metafunction tl-grammar
  wcm-replace : v v ([v v] ...) -> ([v v] ...)
  ; Add it if it is not present
  [(wcm-replace v_k v_v ([v_ki v_vi] ...))
   ([v_k v_v] [v_ki v_vi] ...)
   (side-condition (not (member (term v_k) (term (v_ki ...)))))]
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
   (wcm-merge (wcm-replace v_k v_v ([v_k-fst v_v-fst] ...))
              ([v_k-snd v_v-snd] ...))])

;; Reduction rules
(define (no-blank-wcm? t)
  (not (redex-match tl-grammar (in-hole E (wcm any hole)) t)))

(define -->_tl
  (reduction-relation
   tl-grammar
   
   ; beta
   (~~> ((λ (x_1 ...) e_1) v_1 ...)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        "beta")
   
   ; match
   (~~> (match (K_1 v_1 ...) l_1 ...)
        (subst-e* (x_1 ...) (v_1 ...) e_1)
        (where [(K_1 x_1 ...) => e_1]
               (in-match (K_1 v_1 ...)
                         (l_1 ...)))
        (side-condition (= (length (term (v_1 ...)))
                           (length (term (x_1 ...)))))
        "match")
   
   ; letrec
   (--> (/ Sigma_1 (in-hole E_1 (letrec ([sigma_1 v_1] ...) e_1)))
        (/ (snoc* Sigma_1 ([sigma_1 v_1] ...)) (in-hole E_1 e_1))
        "letrec")
   
   ; sigma
   (--> (/ Sigma_1 (in-hole E_1 ((! sigma_1) v_1 ...)))
        (/ Sigma_1 (in-hole E_1 (subst-e* (x_1 ...) (v_1 ...) e_1)))
        (where (λ (x_1 ...) e_1) (in-Sigma Sigma_1 sigma_1))
        "sigma")
   
   ; match + sigma
   (--> (/ Sigma_1 (in-hole E_1 (match (! sigma_1) l_1 ...)))
        (/ Sigma_1 (in-hole E_1 (match v_1 l_1 ...)))
        (where v_1 (in-Sigma Sigma_1 sigma_1))
        "match + sigma")
   
   ; abort
   (-+> (in-hole E_1 (abort e_1))
        e_1
        "abort")
   
   ; w-c-m install
   #;(-+> (in-hole E_1 (w-c-m v_k v_v e_1))
        (in-hole E_1 (wcm ([v_k v_v]) e_1))
        "w-c-m install")
   
   ; wcm merge
   (-+> (in-hole E_1 (wcm ([v_ki v_vi] ...)
                          (wcm ([v_kj v_vj] ...) e_1)))
        (in-hole E_1 (wcm (wcm-merge ([v_ki v_vi] ...)
                                     ([v_kj v_vj] ...))
                          e_1))
        (side-condition (no-blank-wcm? (term E_1)))
        "wcm merge")
   
   ; wcm return
   (-+> (in-hole E_1 (wcm ([v_ki v_vi] ...) v_2))
        (in-hole E_1 v_2)
        (side-condition (no-blank-wcm? (term E_1)))
        "wcm return")
   
   ; c-c-m
   (-+> (in-hole E_1 (c-c-m v_1 ...))
        (in-hole E_1 (get-marks-tl E_1 (v_1 ...)))
        "c-c-m")
   
   with
   ;; -+> is evaluation independent of store
   [(--> (/ Sigma_1 from)
         (/ Sigma_1 to))
    (-+> from to)]
   ;; ~~> is evaluation in any E:
   [(-+> (in-hole E_1 from)
         (in-hole E_1 to))
    (~~> from to)]))