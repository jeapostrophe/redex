#lang racket

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
     (match x
       [("0") 
        => (match y
             [("0") => ("#t")]
             [("S" yn) => ("#f")])]
       [("S" xn)
        => (match y
             [("0") => ("#f")]
             [("S" yn) => ((! "=") xn yn)])])))

(define +-impl
  `(λ (x y)
     (match x
       [("0") => y]
       [("S" xn)
        => ,(:let 'in '((! "+") xn y)
                  '("S" in))])))

(define --impl
  `(λ (n m)
     (match n
       [("0") => n]
       [("S" k) 
        => (match m
             [("0") => n]
             [("S" l) => ((! "-") k l)])])))

(define *-impl
  `(λ (n m)
     (match n
       [("0") => ("0")]
       [("S" p) => ,(:let 'tmp '((! "*") p m)
                          '((! "+") m tmp))])))

(define if-impl
  `(λ (cond true false)
     (match cond
       [("#t") => (true ("unit"))]
       [("#f") => (false ("unit"))])))

(define unsafe-map-impl
  `(unsafe-λ (f l)
             (match l
               [("nil") => ("nil")]
               [("cons" v l) => 
                             ,(:let 'x '(f v)
                                    (:let 'r '((! "unsafe-map") f l)
                                          '("cons" x r)))])))

(define all-safe?-impl
  `(λ (marks)
     (match marks
       [("nil") => ("#t")]
       [("cons" m l) 
        => (match m
             [("marks" sf)
              => (match sf
                   [("some" v)
                    => (match v
                         [("#t") => ((! "all-safe?") l)]
                         [("#f") => ("#f")])])])])))                  

(define (with-arith e)
  `(letrec
       (["=" ,=-impl]
        ["+" ,+-impl]
        ["-" ,--impl]
        ["*" ,*-impl]
        ["if" ,if-impl])
     ,e))

(define (with-safe e)
  (with-arith
      `(letrec
           (["unsafe-map" ,unsafe-map-impl]
            ["all-safe?" ,all-safe?-impl])
         ,e)))

(define arith-store
  `(snoc (snoc (snoc (snoc (snoc mt ["=" -> ,=-impl])
                           ["+" -> ,+-impl])
                     ["-" -> ,--impl])
               ["*" -> ,*-impl])
         ["if" -> ,if-impl]))
(define safe-store
  `(snoc (snoc ,arith-store
               ["unsafe-map" -> ,unsafe-map-impl])
         ["all-safe?" -> ,all-safe?-impl]))

(define (:if cond true false)
  (:let 'cond-val cond
        `((! "if")
          cond-val
          (λ (unit) ,true)
          (λ (unit) ,false))))

(provide (all-defined-out))
