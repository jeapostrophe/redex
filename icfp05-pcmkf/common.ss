#lang scheme

(define (fact n)
  (if (zero? n)
      1
      (* n (fact (sub1 n)))))

(define (num n)
  (if (zero? n)
      `("0")
      `("S" ,(num (sub1 n)))))

(define (lst l)
  (if (empty? l)
      `("nil")
      `("cons" ,(first l) ,(lst (rest l)))))

(define (:let name named-expr body)
  `((λ (,name) ,body)
    ,named-expr))

(define =-impl
  `(λ (x y)
     (case x
       [("0") 
        => (case y
             [("0") => ("#t")]
             [("S" yn) => ("#f")])]
       [("S" xn)
        => (case y
             [("0") => ("#f")]
             [("S" yn) => ((! "=") xn yn)])])))

(define +-impl
  `(λ (x y)
     (case x
       [("0") => y]
       [("S" xn)
        => ,(:let 'in '((! "+") xn y)
                  '("S" in))])))

(define --impl
  `(λ (n m)
     (case n
       [("0") => n]
       [("S" k) 
        => (case m
             [("0") => n]
             [("S" l) => ((! "-") k l)])])))

(define *-impl
  `(λ (n m)
     (case n
       [("0") => ("0")]
       [("S" p) => ,(:let 'tmp '((! "*") p m)
                          '((! "+") m tmp))])))

(define if-impl
  `(λ (cond true false)
     (case cond
       [("#t") => (true ("unit"))]
       [("#f") => (false ("unit"))])))

(define (with-arith e)
  `(letrec
       (["=" ,=-impl]
        ["+" ,+-impl]
        ["-" ,--impl]
        ["*" ,*-impl]
        ["if" ,if-impl])
     ,e))

(define arith-store
  `(snoc (snoc (snoc (snoc (snoc mt ["=" -> ,=-impl])
                           ["+" -> ,+-impl])
                     ["-" -> ,--impl])
               ["*" -> ,*-impl])
         ["if" -> ,if-impl]))

(define (:if cond true false)
  (:let 'cond-val cond
        `((! "if")
          cond-val
          (λ (unit) ,true)
          (λ (unit) ,false))))

(provide (all-defined-out))