#lang scheme
(require redex)
(provide (all-defined-out))

(define Y_n
  (term
   (λ (f) ((λ (x) (f (x x)))
           (λ (x) (f (x x)))))))

(define Z
  (term
   (λ (f) ((λ (x) (f (λ (y) ((x x) y))))
           (λ (x) (f (λ (y) ((x x) y))))))))
(define Y_v Z)

(define (Num n)
  (term
   (λ (f)
     (λ (x)
       ,(let loop ([n n])
          (if (zero? n)
              (term x)
              (term (f ,(loop (sub1 n))))))))))

(define succ
  (term
   (λ (n)
     (λ (f)
       (λ (x)
         (f ((n f) x)))))))

(define plus
  (term
   (λ (m)
     (λ (n)
       (λ (f)
         (λ (x)
           ((n f) ((m f) x))))))))

(define mult
  (term
   (λ (m)
     (λ (n)
       (λ (f)
         (m (n f)))))))

(define pred
  (term
   (λ (n)
     (λ (f)
       (λ (x)
         (((n (λ (g) (λ (h) (h (g f)))))
           (λ (u) x))
          (λ (u) u)))))))

(define true
  (term
   (λ (x) (λ (y) x))))
(define false
  (term
   (λ (x) (λ (y) y))))

(define iszero
  (term
   (λ (n) ((n (λ (x) ,false)) ,true))))

(define factorial
  (term
   (λ (fac)
     (λ (n)
       (((,iszero n) ,(Num 1))
        ((,mult n) (fac (,pred n))))))))
