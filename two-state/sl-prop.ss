#lang scheme
(require redex/reduction-semantics
         "set.ss"
         "sl.ss"
         "common.ss")

(define result?
  (redex-match sl-grammar (/ Sigma v)))

(define (open? p)
  (not (set-empty? (term (free-vars_sl ,p)))))

(define (progress? p)
  (or (open? p)
      (result? p)
      (not (= 0 (length (apply-reduction-relation -->_sl p))))))

(redex-check sl-grammar e* (progress? (term e*)))

(define well-formed?
  (redex-match sl-grammar e*))

(define (preservation? p)
  (or (open? p)
      (andmap (λ (q)
                (and (well-formed? q)
                     (not (open? q))))
              (apply-reduction-relation -->_sl p))))

(redex-check sl-grammar e* (preservation? (term e*)))

(define (safety? p)
  (define fvs (term (free-vars_sl ,p)))
  (define nexts (apply-reduction-relation -->_sl p))
  (or (result? p)
      (and (empty? nexts)
           (open? p))
      (and (not (empty? nexts))
           (andmap (λ (q)
                     (and (well-formed? q)
                          (subset? (term (free-vars_sl ,q))
                                   fvs)))
                   nexts))))

(define (safety?-check p)
  (define fvs (term (free-vars_sl ,p)))
  (define nexts (apply-reduction-relation -->_sl p))
  `(let ([fvs ,fvs])
     (or ,(result? p)
         (and ,(empty? nexts)
              ,(open? p))
         (and ,(not (empty? nexts))
              ,@(map (λ (q)
                       `(let ([q ,q]
                              [qfvs ,(term (free-vars_sl ,q))])
                          (and ,(well-formed? q)
                               ,(subset? (term (free-vars_sl ,q))
                                         fvs))))
                     nexts)))))

(redex-check sl-grammar e* (safety? (term e*)))

