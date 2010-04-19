;
; cbneed_AF_db.ss
; standard reduction machine for AF calculus using db indices
;

#lang scheme
(require redex)
(require srfi/1)
(require test-engine/scheme-tests)


(define-language λ-calculus
  ((M N L) x (λ x M) (M M))
  ((x y z) variable-not-otherwise-mentioned)
  )

(define-extended-language λ-need λ-calculus
  (V (λ x M))       ; values
  (A V ((λ x A) M)) ; answers
  (E hole           ; contexts
     (E M) 
     ((λ x_1 (in-hole E x_1)) E) 
     ((λ x E) M))
  )


(define-language λ-db
  (n number)
  ((M N L) n (λ M) (M M)))
           
(define-extended-language λ-db-need λ-db
  (V (λ M))           ; values
  (A V ((λ A) M))
  (E hole             ; contexts
     (E M)
     ((λ E) M)
     (side-condition
      ((λ (in-hole E_1 n_1)) E)
      (= (term (∆ E_1)) (term n_1)))
     )
  )

(define-metafunction λ-db-need
  [(∆ hole) 
   0]
  [(∆ (E M)) 
   (∆ E)]
  [(∆ ((λ E) M)) 
   ,(add1 (term (∆ E)))]
  [(∆ ((λ (in-hole E_1 n)) E)) 
   (∆ E)
   (side-condition (= (term (∆ E_1)) (term n)))]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; db and _db
;; 
;; Converts a regular λ-need term to one using de bruijn indices
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-metafunction λ-need
  [(db M) (_db M ())])

; Variables are 0-based. So a variable indicates the number of bindings between
; the variable and its binding (not including the actual binding for the variable).
; So (db (λ x x)) -> (λ 0)
(define-metafunction λ-need
  [(_db x (y ...)) 
   ,(list-index (lambda (y) (equal? y (term x))) (term (y ...)))]
  [(_db (λ x M) (y ...)) 
   (λ (_db M (x y ...)))]
  [(_db (M N) (y ...)) 
   ((_db M (y ...)) (_db N (y ...)))]
  )

(define (db-test-suite)
  (test-equal (term (db (λ x x))) 
              (term (λ 0)) )
  (test-equal (term (db (λ x (λ y (x y)))))
              (term (λ (λ (1 0)))) )
  (test-equal (term (db (λ x (x (λ y x)))))
              (term (λ (0 (λ 1)))) )
  (test-equal (term (db (λ x (x (λ x x)))))
              (term (λ (0 (λ 0)))) )
  (test-equal (term (db (λ x (λ y (x (λ z (y (x z))))))))
              (term (λ (λ (1 (λ (1 (2 0))))))) )

  (test-results)
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (inc-FVs M n)
;; increment all free variables in M by n
(define-metafunction λ-db-need
  [(inc-FVs M n) (_inc-FVs M n 0)]
  )

; (_inc-FVs M n_1 n_2)
; Helper function used by inc-FVs
; Increment all free variables in M by n_1. n_2 keeps track of the # of λs
; seen so far. A free variable is one that is >= n_2.
(define-metafunction λ-db-need
  [(_inc-FVs n n_1 n_2)
   ,(+ (term n) (term n_1))
   (side-condition (>= (term n) (term n_2)))]
  [(_inc-FVs n n_1 n_2)
   n]
  [(_inc-FVs (M N) n_1 n_2)
   ((_inc-FVs M n_1 n_2) (_inc-FVs N n_1 n_2))]
  [(_inc-FVs (λ M) n_1 n_2)
   (λ (_inc-FVs M n_1 ,(add1 (term n_2))))]
 )

(define (inc-FVs-test-suite)
  (test-equal (term (inc-FVs (λ 0) 0) )
              (term (λ 0) ) )
  (test-equal (term (inc-FVs (λ 0) 1) )
              (term (λ 0) ) )
  (test-equal (term (inc-FVs (λ (1 0)) 0) )
              (term (λ (1 0)) ) )
  (test-equal (term (inc-FVs (λ (1 0)) 1) )
              (term (λ (2 0)) ) )
  (test-equal (term (inc-FVs (λ (1 0)) 2) )
              (term (λ (3 0)) ) )
  (test-equal (term (inc-FVs (λ (λ (1 0))) 2) )
              (term (λ (λ (1 0))) ) )
  (test-equal (term (inc-FVs ((1 2) 3) 0) )
              (term ((1 2) 3) ) )
  (test-equal (term (inc-FVs ((1 2) 3) 4) )
              (term ((5 6) 7) ) )
  
  (test-results)
  )



(define λ-db-need-red
  (reduction-relation
   λ-db-need
   [--> ( in-hole 
          E
          ((λ (in-hole E_1 n)) V) )
        ( in-hole
          E
          ((λ (in-hole E_1 (inc-FVs V ,(add1 (term n))))) V) )
        (side-condition (= (term (∆ E_1)) (term n)))
        deref]
   
   [--> ( in-hole
          E
          (((λ A) M) N) )
        ( in-hole
          E
          ((λ (A (inc-FVs N 1))) M) )
        assoc-L]
   
   [--> ( in-hole
          E
          ((λ (in-hole E_1 n)) ((λ A) M)) )
        ( in-hole
          E
          ((λ ((inc-FVs (λ (in-hole E_1 n)) 1) A)) M) )
        (side-condition (= (term (∆ E_1)) (term n)))
        assoc-R]
   
   ))
  
; makes an xx machine term, which is a term and a stack (list) of contexts
(define (make-db-need-red-term t)
;  (term (,t () ,(list (term mt))))
  (term ,t)
  )

; test suite for cbneed xx machine
(define (TEST-db-need-red exp)
  (lambda (expected)
    (define λ-db-need-red-answers
      (apply-reduction-relation* λ-db-need-red 
                                 (make-db-need-red-term (term (db ,exp)))))
    (and (equal? (length λ-db-need-red-answers) 1)
         (equal? expected (term ,(car λ-db-need-red-answers)))))
  )

; (traces λ-db-cek (make-db-cek-term (term (db ((λ x x) (λ x x)) ))))

(define (run-db-need-red-test-suite)
  ;;;;;;;;;; db 0 tests ;;;;;;;;;;
  (test-predicate 
   (TEST-db-need-red (term ((λ x x) (λ x x)) ) )
   (term ((λ (λ 0)) (λ 0)) ) )
  (test-predicate
   (TEST-db-need-red (term ((λ x x) ((λ x x) (λ x x))) ) )
   (term ((λ ((λ (λ 0)) (λ 0))) (λ 0)) ) )
  (test-predicate
   (TEST-db-need-red (term (((λ x x) (λ x x)) (λ x x)) ) )
   (term ((λ ((λ (λ 0)) (λ 0))) (λ 0)) ) )
  
  ; needs side condition in deref
  (test-predicate
   (TEST-db-need-red (term (((λ x x) (λ x x)) ((λ x x) (λ x x))) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  
  (test-predicate 
   (TEST-db-need-red (term ((λ x (x x)) (λ x x)) ) )
   (term ((λ ((λ (λ 0)) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x (x (x x))) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x ((x x) x)) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x ((x x) (x x))) (λ x x)) ) )
   (term ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0))) (λ 0)) ) )
  
  (test-predicate
   (TEST-db-need-red (term ((λ x (((λ x x) (λ x x)) x)) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x (x ((λ x x) (λ x x)))) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x (x (x (λ x x)))) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red (term ((λ x (x ((λ x x) x))) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )

  
  ; machine doesnt garbage collect
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (x x)) x)) (λ y y)) ) )
;   (term (λ x x)) )  
  
  ;;;;;;;;;; db 1+ tests ;;;;;;;;;;
  (test-predicate
   (TEST-db-need-red (term ((λ x ((λ y (x y)) (λ x x))) (λ x x)) ) )
   (term ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)) ) )

  ; needs renaming in deref
  ; needs side condition in ∆ metafunction
  (test-predicate
   (TEST-db-need-red (term ((λ x ((λ x ((((λ y (x y)) (λ y (y x))) (λ x x)) (λ x x))) (λ z (x z)))) (λ x x)) ) )
   (term 
    ((λ ((λ ((λ ((λ ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0)))
                             (λ (6 0))))
                         (λ 0)))
                     (λ (0 3))))
                 (λ (0 2))))
             (λ (0 1))))
         (λ (1 0))))
     (λ 0))) )
  
  ; test renaming in assoc-R
  ; needs renaming in assoc-R rule
  ; if no capture, result should be (λ z z)
  ; but with capture, result will be (λ w w)
  (test-predicate
   (TEST-db-need-red (term ((λ x ((λ y (y x)) ((λ x (λ y (x y))) (λ w (x w))))) (λ z z)) ) )
   (term 
    ((λ ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)))
             (λ (1 0))))
         (λ (1 0))))
     (λ 0)) ) )
  
  ; needs side-condition in assoc-R rule
  (test-predicate
   (TEST-db-need-red (term ((λ x (((λ y (x y)) ((λ x (λ y (x y))) (λ w (w x)))) (λ x x))) (λ z z)) ) )
   (term 
    ((λ ((λ ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)))
                 (λ (2 0))))
             (λ (1 0))))
         (λ (0 1))))
     (λ 0)) ) )
  
  ; test renaming in assoc-L
  ; if no capture, result should be (λ z z), 
  ; but with capture, result will be (λ w w)
  (test-predicate
   (TEST-db-need-red (term ((λ x (((λ x (λ y (x y))) (λ w (w x))) x)) (λ z z)) ) )
   (term 
    ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)))
         (λ (0 1))))
     (λ 0)) ) )
  
  ; test renaming in beta-need
  (test-predicate
   (TEST-db-need-red (term ((λ x ((λ y (y (λ x (y x)))) (λ y (y x)))) (λ z z)) ) )
   (term 
    ((λ ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0)))
             (λ (1 0))))
         (λ (0 1))))
     (λ 0)) ) )  
  
  
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (x y)) x)) (λ y y)) ) )
;   (term (λ x x)) )
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (x y)) x)) ((λ x ((λ y (x y)) x)) (λ y y))) ) )
;   (term (λ x x)) )

  ; problem with the db cek machine
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (y x)) (λ x x))) (λ y y)) ) )
;   (term (λ x x)) )
  ; We can't just decrement leftover var bc then the lookup in the environment
  ; will be incorrectly successful (when we really want to search for a bind
  ; in the control stack). This example shows why we can't both decrement 
  ; leftover vars and truncate environment -- because other vars still may 
  ; need values bound in env.
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (y (x y))) (λ x x))) (λ y y)) ) )
;   (term (λ x x)) )
;  (test-predicate
;   (TEST-db-need-red (term ((λ x ((λ y (y (y x))) (λ x x))) (λ y y)) ) )
;   (term (λ x x)) )
  
  
;  ; test assoc-R
;  (test-predicate 
;   (TEST-xx (term ((λ x x) ((λ x (λ y (x y))) (λ x x)))) )
;   (term ((λ z (λ y1 (z y1))) (λ x x))) )
;  ; no garbage collection
;  (test-predicate 
;   (TEST-xx (term ((λ x (λ y y)) ((λ x (λ y (x y))) (λ x x)))) )
;   (term ((λ x (λ y y)) ((λ x (λ y (x y))) (λ x x)))) )
;  (test-predicate 
;   (TEST-xx (term ((λ x x) ((λ x (λ y (y x))) (λ x x)))) )
;   (term ((λ z (λ y1 (y1 z))) (λ x x))) )
;  (test-predicate
;   (TEST-xx (term ((λ x x) ((λ z ((λ y (λ x x)) (λ y y))) (λ z z)))) )
;   (term ((λ z1 ((λ y (λ x1 x1)) (λ y y))) (λ z z))) )
;  
;  (test-predicate 
;   (TEST-xx (term ((λ x x) ((λ x ((λ y (x y)) (λ x x))) (λ x x)))) )
;   (term (λ x x)) )
;  (test-predicate 
;   (TEST-xx (term ((λ x x) ((λ x ((λ y (y x)) (λ x x))) (λ x x)))) )
;   (term (λ x x)) )
;  
  ; test assoc-L
;  (test-predicate
;   (TEST-db-need-red (term (((λ x (λ y (y x))) (λ x x)) (λ z z)) ) )
;   (term (λ x x)) )
;  (test-predicate
;   (TEST-xx (term (((λ x (λ y (x y))) (λ x x)) (λ z z))) )
;   (term (λ z2 z2)) )
;  (test-predicate
;   (TEST-xx (term (((λ z ((λ y (λ x x)) (λ y y))) (λ z z)) (λ x x)) ) )
;   (term ((λ z1 ((λ y (λ x x)) (λ y y))) (λ z z))) )
;  (test-predicate
;   (TEST-xx (term (((λ x ((λ z (λ y (z y))) (λ x x))) (λ y y)) (λ z z))) )
;   (term ((λ z1 (λ z z)) (λ y y))) )
;  
;  (test-predicate
;   (TEST-xx (term (((λ x ((λ y (y x)) (λ x x))) (λ x x)) (λ z z))) )
;   (term (λ z z)) )
;  (test-predicate
;   (TEST-xx (term (((λ x ((λ y (x y)) (λ x x))) (λ x x)) (λ z z))) )
;   (term (λ z z)) )
;  
  (test-predicate
   (TEST-db-need-red paper-example1)
   (term 
    ((λ ((λ ((λ ((λ ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0)))
                         (λ 0)))
                     (λ 0)))
                 (λ 0)))
             (λ (1 0))))
         (λ 0)))
     (λ 0)) ) )
  (test-predicate 
   (TEST-db-need-red paper-example2)
   (term ((λ ((λ ((λ ((λ (λ 0)) (λ 0))) (λ 0))) (λ 0))) (λ 0)) ) )
  (test-results))


;; test cases from AF paper
(define paper-example1
  (term 
    ( (λ f ((f (λ x x)) (f (λ x x))))
      ((λ z (λ w (z w))) ((λ x x) (λ x x))) )
    ))
(define paper-example2
  (term
    ( ( (λ z (λ w (z w))) 
        ((λ x x) (λ x x)) )
      (λ x x) )
    ))