#lang racket
(require redex/reduction-semantics
         "set.rkt"
         "tl.rkt"
         "common.rkt")

(define result?
  (redex-match tl-grammar (/ Sigma v)))

(define (open? p)
  (not (set-empty? (term (free-vars_tl ,p)))))

(define (progress? p)
  (or (open? p)
      (result? p)
      (not (= 0 (length (apply-reduction-relation -->_tl p))))))

(redex-check tl-grammar e* (progress? (term e*)))

(define well-formed?
  (redex-match tl-grammar e*))

(define (preservation? p)
  (or (open? p)
      (andmap (λ (q)
                (and (well-formed? q)
                     (not (open? q))))
              (apply-reduction-relation -->_tl p))))

(redex-check tl-grammar e* (preservation? (term e*)))

(define (safety? p)
  (define fvs (term (free-vars_tl ,p)))
  (define nexts (apply-reduction-relation -->_tl p))
  (or (result? p)
      (and (empty? nexts)
           (open? p))
      (and (not (empty? nexts))
           (andmap (λ (q)
                     (and (well-formed? q)
                          (subset? (term (free-vars_tl ,q))
                                   fvs)))
                   nexts))))

(define (safety?-check p)
  (define fvs (term (free-vars_tl ,p)))
  (define nexts (apply-reduction-relation -->_tl p))
  `(let ([fvs ,fvs])
     (or ,(result? p)
         (and ,(empty? nexts)
              ,(open? p))
         (and ,(not (empty? nexts))
              ,@(map (λ (q)
                       `(let ([q ,q]
                              [qfvs ,(term (free-vars_tl ,q))])
                          (and ,(well-formed? q)
                               ,(subset? (term (free-vars_tl ,q))
                                         fvs))))
                     nexts)))))

(redex-check tl-grammar e* (safety? (term e*)))

