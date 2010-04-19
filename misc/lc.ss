#lang scheme
(require redex
         redex/gui)

(define-language lang
  (e (lambda (x) e)
     (e e)
     x)
  (e-ctxt (lambda (x) e-ctxt)
          a-ctxt)
  (a-ctxt (a-ctxt e)
          (x a-ctxt)
          hole)
  (v (lambda (x) e)
     x)
  (x variable))

(define red
  (reduction-relation
   lang
   (--> (in-hole e-ctxt_1 ((lambda (x_1) e_body) e_arg))
        (in-hole e-ctxt_1 (subst (x_1 e_arg e_body)))
        beta)))

(define-metafunction lang
  [(subst (x_1 e_1 (lambda (x_1) e_2))) (lambda (x_1) e_2)]
  [(subst (x_1 e_1 (lambda (x_2) e_2))) 
   ,(term-let ((x_new (variable-not-in (term e_1) (term x_2))))
              (term (lambda (x_new) (subst (x_1 e_1 (subst (x_2 x_new e_2)))))))]
  [(subst (x_1 e_1 x_1)) e_1]
  [(subst (x_1 e_1 x_2)) x_2]
  [(subst (x_1 e_1 (e_2 e_3)))
   ((subst (x_1 e_1 e_2))
    (subst (x_1 e_1 e_3)))])

(traces red '((lambda (x) (x x)) (lambda (x) (x x))))

(define Y '(lambda (f) 
             ((lambda (x) (f (x x)))
              (lambda (x) (f (x x))))))

(define zero '(lambda (f)
                (lambda (x)
                  x)))
(define succ '(lambda (n)
                (lambda (f)
                  (lambda (x) 
                    (f ((n f)
                        x))))))
(define plus '(lambda (m)
                (lambda (n)
                  (lambda (f) 
                    (lambda (n)
                      ((n f)
                       ((m f)
                        x)))))))
(define mult '(lambda (m)
                (lambda (n) 
                  (lambda (f)
                    (m (n f))))))
(define pred '(lambda (n)
                (lambda (f)
                  (lambda (x)
                    (((n (lambda (g) (lambda (h) (h (g f)))))
                      (lambda (u) x))
                     (lambda (u) u))))))

(define true '(lambda (x)
                (lambda (y)
                  x)))
(define false '(lambda (x)
                 (lambda (y)
                   y)))

(define iszero `(lambda (n) 
                  ((n (lambda (x) ,false))
                   ,true)))

(define fac `(lambda (f)
               (lambda (n)
                 (((,iszero n) (,succ ,zero))
                  ((,mult n) (f (,pred n)))))))

(traces red `(,iszero ,zero))
(traces red `(,iszero (,succ ,zero)))

(traces red `((,Y ,fac) ,zero))
