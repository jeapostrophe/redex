#lang scheme
(require redex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expression grammar:

;; `core-grammar' is typeset for the paper, but `grammar'
;; extends it with some standard things (such as arithmetic,
;; assignment, and output) to make testing easier.

(define-language core-grammar
  ;; Expressions
  ;;  Constrain `wcm' so that it can't
  ;;  wrap an immediate `wcm':
  (e m (wcm w m))
  (m x v (e e ...) (begin e e) (% e e e)) 
  
  ;; Values
  (v (list v ...) (λ (x ...) e) (cont v (hide-hole E)) (comp (hide-hole E))
     abort current-marks
     cons u)
  (n number)
  
  ;; Primitives that need a wcm wrapper:
  (u call/cc call/comp call/cm)
  
  ;; Variables
  (x (variable-except λ if begin set!
                      call/cc cont 
                      % call/comp abort comp
                      call/cm wcm current-marks
                      zero? + print cons list first rest
                      * <>))
  
  ;; `wcm' bindings
  (w ((v v) ...))
  
  ;; Evaluation contexts
  ;;  Constrain `wcm' so it can't wrap a `wcm'.
  ;;  General evalation context:
  (E M (wcm w M))
  (M hole (v ... E e ...) (begin E e) (% v E v)))

(define-extended-language grammar core-grammar
  (p (<> s       ; store
         (o ...) ; output
         e))     ; expression
  
  (m ....
     (if e e e)
     (set! x e))
  (bool #f #t)
  (v ....
     n bool
     zero? print + first rest)
  
  ;; Store
  (s ([x v] ...))
  
  ;; Output
  (o number)
  
  (M ....
     (set! x E)
     (if E e e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Debugging:

(define-syntax (define-language-predicates stx)
  (syntax-case stx ()
    [(_ id)
     (with-syntax ([? (datum->syntax
                       #'id
                       (string->symbol (format "~s?" (syntax-e #'id)))
                       #'id)])
       #'(define ? (redex-match grammar id)))]
    [(_ id ...)
     #'(begin (define-language-predicates id) ...)]))

(define-language-predicates p e x v E)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide core-grammar grammar
         p? e? x? v? E?)