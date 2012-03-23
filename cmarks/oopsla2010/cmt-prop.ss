#lang scheme
(require redex/reduction-semantics
         tests/eli-tester
         "common.ss"
         "sl.ss"
         "tl.ss"
         "cmt.ss")

(define cmt-decompose?
  (term-match/single
   sl-grammar+cmt
   [a #t]
   [(in-hole EE r) #t]))  

(redex-check sl-grammar e (cmt-decompose? (term e)))

(printf "Done with decompose~n")

(define-language reasonable-sl-programs
  [se sa
      (sw ... se) 
      (letrec ([sigma sv] ...) se)
      (match sw sl ...)
      (call/cc sw)]
  [sl [(K x ...) => se]
      [else => se]]
  [sa sw
      (K sa ...)]
  [sw sv
      x]
  [sv (! sigma) ; XXX not good
      (λ (x ...) se)
      (unsafe-λ (x ...) ue)
      (K sv ...)
      (cont (hide-hole E))]
  
  [ue ua
      (uw ... ue) 
      (letrec ([sigma uv] ...) ue)
      (match uw ul ...)]
  [ul [(K x ...) => ue]
      [else => ue]]
  [ua uw
      (K ua ...)]
  [uw uv
      x]
  [uv (! sigma) ; XXX not good
      (λ (x ...) ue)
      (K uv ...)]
  
  [x variable-not-otherwise-mentioned]
  [K string]
  [sigma 
   (side-condition (name t string)
                   (not (member (term t) 
                                '("resume" "call/cc" "=" "+" "-" "*" "if" "unsafe-map" "all-safe?"))))]
  
  [Sigma mt
         (snoc Sigma [sigma -> sv])]
  [e* (/ Sigma e)]
  
  [E hole
     (sv ... E)]
  [TE (/ Sigma E)])

(test
 (redex-match reasonable-sl-programs se (term (call/cc (unsafe-λ (mt) q)))) => #f
 (redex-match reasonable-sl-programs se (term (letrec (("call/cc" (λ (n x) (call/cc d)))) (call/cc (cont hole))))) => #f)

(define remove-letrec_rel
  (reduction-relation
   tl-grammar
   (--> (in-hole E_1 (letrec ([sigma v] ...) e))
        (in-hole E_1 e))))

(define (remove-letrec e)
  (first (apply-reduction-relation* remove-letrec_rel e)))

(define (alpha-equal? t1 t2)
  (define t1->t2 (make-hash))
  (define matchit
    (match-lambda*
      [(list `(λ (,id1 ...) . ,rest1)
             `(λ (,id2 ...) . ,rest2))
       (define old
         (map (λ (i) (hash-ref t1->t2 i #f)) id1))
       (for-each (curry hash-set! t1->t2)
                 id1 id2)
       (begin0 (matchit rest1 rest2)
               (for-each (λ (i old)
                           (if old
                               (hash-set! t1->t2 i old)
                               (hash-remove! t1->t2 i)))
                         id1 old))]
      [(list (cons t1_f t1_r)
             (cons t2_f t2_r))
       (and (matchit t1_f t2_f)
            (matchit t1_r t2_r))]
      [(list (? string? s1)
             (? string? s2))
       (string=? s1 s2)]
      [(list (? symbol? s1)
             (? symbol? s2))
       (symbol=? (hash-ref! t1->t2 s1 s2) s2)]
      [(list (list) (list)) #t]
      [else #f]))
  (matchit t1 t2))

(test
 (alpha-equal? (term (λ (x) (abort ((! "resume") ("cons" ("marks" ("some" (λ (x) (x)))) ("nil")) x))))
               (term (λ (x1) (abort ((! "resume") ("cons" ("marks" ("some" (λ (x) (x)))) ("nil")) x1))))))

(define value? (redex-match sl-grammar v))

(define ((make-cmt-correct? cmt-compatible?) sl)
  (define sl-answers
    (apply-reduction-relation* -->_sl (term (/ mt ,(with-safe sl)))))
  (define tl (CMT sl 'safe))
  (define tl-answers
    (apply-reduction-relation* -->_tl (term (/ mt ,tl))))
  (andmap
   (lambda (sl-ans tl-ans)
     (match-let ([`(/ ,sl-store ,sl-val) sl-ans]
                 [`(/ ,tl-store ,tl-val) tl-ans])
       (cmt-compatible? sl-val tl-val)))
   sl-answers
   tl-answers))

;;;;;;;;;;;

(define-language pure-sl-programs
  [se sa
      (sw ... se) 
      (letrec ([sigma sv] ...) se)
      (match sw sl ...)
      (call/cc sw)]
  [sl [(K x ...) => se]
      [else => se]]
  [sa sw
      (K sa ...)]
  [sw sv
      x]
  [sv (! sigma) ; XXX not good
      (λ (x ...) se)
      (K sv ...)
      (cont (hide-hole E))]
  
  [x variable-not-otherwise-mentioned]
  [K string]
  [sigma 
   (side-condition (name t string)
                   (not (member (term t) 
                                '("resume" "call/cc" "=" "+" "-" "*" "if" "unsafe-map" "all-safe?"))))]
  
  [Sigma mt
         (snoc Sigma [sigma -> sv])]
  [e* (/ Sigma e)]
  
  [E hole
     (sv ... E)]
  [TE (/ Sigma E)])

(define (pure-cmt-compatible? sl-val tl-val-ext)
  (define tl-val-int (remove-letrec (CMT sl-val 'safe)))
  (define ans 
    (or (not (value? sl-val))
        (alpha-equal? tl-val-int tl-val-ext)))
  (unless ans
    (printf "SL:~n~S~nTL int:~n~S~nTL ext:~n~S~n"
            sl-val tl-val-int tl-val-ext))
  ans)

(define pure-cmt-correct? (make-cmt-correct? pure-cmt-compatible?))

(redex-check pure-sl-programs se (pure-cmt-correct? (term se)))

;;;;;;;;;;;
(define (reasonable-cmt-compatible? sl-val tl-val-ext)
  (define tl-val-int (remove-letrec (CMT sl-val 'safe)))
  (define ans 
    (or (not (value? sl-val))
        (alpha-equal? tl-val-int tl-val-ext)
        (equal? tl-val-ext '("unsafe context"))))
  (unless ans
    (printf "SL:~n~S~nTL int:~n~S~nTL ext:~n~S~n"
            sl-val tl-val-int tl-val-ext))
  ans)

(define reasonable-cmt-correct? (make-cmt-correct? reasonable-cmt-compatible?))

(test
 (reasonable-cmt-correct? (term ((unsafe-λ (f)
                                ,(:let 'x `(f ,(num 2))
                                       `((! "+") x ,(num 1))))
                      (λ (y) (call/cc (λ (k) (k ,(num 3))))))))
 (reasonable-cmt-correct? (term ((! "We") (cont hole) (unsafe-λ () W) (cont hole) (unsafe-λ (w oB h) R) (λ (DC I IB d O) (call/cc v)) (! "yNYOXg") ("letrec" L I))))
 (reasonable-cmt-correct? (term ((call/cc (cont hole)))))
 (reasonable-cmt-correct? (term (letrec (("" (cont ((cont hole) (cont hole) (! "f") (cont hole) (cont hole) hole))) ("rquQ" (! "λ")) ("BskzdU" (cont ((! "match") hole))) ("oiOv" (cont (hole))) ("" (unsafe-λ (B) G)) ("oBVASDiJI" (λ () (Y u r (call/cc ZK)))) ("EBVcnxCKqOe" ("AIqpVLp" (! "i")))) (P y (cont hole) x)))))

(redex-check reasonable-sl-programs se (reasonable-cmt-correct? (term se)))