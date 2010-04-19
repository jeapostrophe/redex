#lang scheme
(require redex)

(define-language lc-lang
  (e (e e)
     (e [x -> v])
     (op e e)
     x
     v)
  (op + *)
  (c (v c)
     (c e)
     (op v c)
     (op c e)
     hole)
  (v number
     (lambda (x) e))
  (x variable-not-otherwise-mentioned))

(define lc-reds
  (reduction-relation
   lc-lang
   ; subst
   (--> (in-hole c_1 ((e_1 e_2) [x -> v_1]))
        (in-hole c_1 ((e_1 [x -> v_1]) (e_2 [x -> v_1])))
        subst-app)
   (--> (in-hole c_1 ((op e_1 e_2) [x -> v_1]))
        (in-hole c_1 (op (e_1 [x -> v_1]) (e_2 [x -> v_1])))
        subst-op)
   (--> (in-hole c_1 (x [x -> v]))
        (in-hole c_1 v)
        subst-id)
   (--> (in-hole c_1 (x_m [x -> v]))
        (in-hole c_1 x_m)
        subst-id-miss
        (side-condition (not (equal? (term x_m) (term x)))))
   (--> (in-hole c_1 (number [x -> v]))
        (in-hole c_1 number)
        subst-num)
   (--> (in-hole c_1 ((lambda (x) e) [x -> v]))
        (in-hole c_1 (lambda (x) e))
        subst-lam-same)
   (--> (in-hole c_1 ((lambda (x_m) e) [x -> v]))
        (in-hole c_1 (lambda (x_m) (e [x -> v])))
        subst-lam-miss
        (side-condition (not (equal? (term x_m) (term x)))))   
   ; real steps
   (--> (in-hole c_1 (+ v_1 v_2))
        (in-hole c_1 ,(+ (term v_1) (term v_2)))
        delta-+)
   (--> (in-hole c_1 (* v_1 v_2))
        (in-hole c_1 ,(* (term v_1) (term v_2)))
        delta-*)
   (--> (in-hole c_1 ((lambda (x_i) e_body) v_i))
        (in-hole c_1 (e_body [x_i -> v_i]))
        beta-v)))

(traces lc-reds
        '((lambda (square)
            (+ (square 5)
               (square 2)))
          (lambda (x) (* x x))))