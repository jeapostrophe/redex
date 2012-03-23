#lang racket
(define (set-sub s l)
  (match s
    [(cons x y)
     (cons (set-sub x l) (set-sub y l))]
    [(? string?)
     (if (member s l)
         empty
         s)]
    [(? symbol?)
     (if (memq s l)
         empty
         s)]
    [(? empty?)
     empty]))

(define set-empty?
  (match-lambda
    [(? empty?) #t]
    [(cons x y)
     (and (set-empty? x) (set-empty? y))]
    [else #f]))  

(define (set-member? x s)
  (match s
    [(? empty?) #f]
    [(? string?) (equal? s x)]
    [(? symbol?) (eq? s x)]
    [(cons s1 s2)
     (or (set-member? x s1) (set-member? x s2))]))    

(define (subset? s1 s2)
  (match s1
    [(? empty?) #t]
    [(? string?) (set-member? s1 s2)]
    [(? symbol?) (set-member? s1 s2)]
    [(cons x y)
     (and (subset? x s2) (subset? y s2))]))

(provide (all-defined-out))
