#lang racket/base
(require redex/pict
         redex/reduction-semantics
         (for-syntax racket/base
                     racket/syntax))

(define-syntax (define-lw stx)
  (syntax-case stx (term)
    [(_ id (term e))
     (with-syntax
         ([id:lw (format-id #'id "~a:lw" #'id)])
       (syntax/loc stx
         (begin
           (define-values
             (id id:lw)
             (values (term e)
                     (to-lw e)))
           (provide id:lw))))]))

(provide define-lw)
