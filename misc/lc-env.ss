#lang scheme
(require redex)

(define-language lc-lang
  (e (e e)
     (op e e)
     x
     v)
  (op + *)
  (c (with x v c)
     (v c)
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
   ; lookup
   (--> (in-hole c_1 x)
        (in-hole c_1 (lc-lookup x c_1))
        lookup)
   (--> (in-hole c_1 (with x v_1 v_2))
        (in-hole c_1 v_2)
        with-ret)
   ; reds
   (--> (in-hole c_1 (+ v_1 v_2))
        (in-hole c_1 ,(+ (term v_1) (term v_2)))
        delta-+)
   (--> (in-hole c_1 (* v_1 v_2))
        (in-hole c_1 ,(* (term v_1) (term v_2)))
        delta-*)
   (--> (in-hole c_1 ((lambda (x_i) e_body) v_i))
        (in-hole c_1 (with x_i v_i e_body))
        beta-v)))

(define-metafunction lc-lang
  lc-lookup : x c -> any
  [(lc-lookup x (with x v c))
   (right v (lc-lookup x c))]
  [(lc-lookup x (with x_m v c))
   (lc-lookup x c)]
  [(lc-lookup x (v c))
   (lc-lookup x c)]
  [(lc-lookup x (c e))
   (lc-lookup x c)]
  [(lc-lookup x (op v c))
   (lc-lookup x c)]
  [(lc-lookup x (op c e))
   (lc-lookup x c)]
  [(lc-lookup x hole)
   hole])

(define-metafunction lc-lang
  right : any any -> any
  [(right hole hole)
   hole]
  [(right hole v)
   v]
  [(right v hole)
   v]
  [(right v_1 v_2)
   v_2])
 
(traces lc-reds
        '((lambda (square)
            (+ (square 5)
               (square 2)))
          (lambda (x) (* x x))))