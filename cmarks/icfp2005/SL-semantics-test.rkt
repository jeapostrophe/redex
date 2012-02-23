#lang racket

(require "SL-syntax.rkt"
         "SL-semantics.rkt"
         "common.rkt"
         "test-util.rkt"
         redex)

(test-SL-result
 ∅ 
 ((λ (x) ("S" x)) ("Z"))
 ("S" ("Z")))

(test-SL-stuck ∅ ((λ (x) ("S" x)) ("Z") ("Z")))

(test-SL-result
 ∅
 (match ("a" ("1"))
   [("a" x) x]
   [("b" y) y])
 ("1"))

(test-SL-result
 ∅
 (match ("b" ("1"))
   [("a" x) x]
   [("b" y) y])
 ("1"))

(test-SL-stuck
 ∅
 (match ("a" ("1"))
   [("a" x) x]
   [("a" y) y]))

(test-SL-result
 ∅
 (letrec ([(ref build-list)
           (λ (n f)
             (match n
               [("Z") ("nil")]
               [("S" m) 
                ((λ (x)
                   ((λ (xs) ("cons" x xs))
                    ((ref build-list) m f)))
                 (f m))]))])
   ((ref build-list) ("S" ("S" ("S" ("Z")))) (λ (i) ("S" i))))
 ("cons" ("S" ("S" ("S" ("Z"))))
         ("cons" ("S" ("S" ("Z")))
               ("cons" ("S" ("Z"))
                     ("nil")))))

(test-SL-result
 ∅
 ((λ (clobber)
    ((λ (a)
       ((λ (b) (a))
        (clobber ("b"))))
     (clobber ("a"))))
  (λ (x)
    (letrec ([(ref y) (λ () x)])
      (ref y))))
 ("b"))

(test-SL-result
 ∅
 (letrec ([(ref x) ("S" ("Z"))])
   (match (ref x)
     [("Z") ("a")]
     [("S" _) ("b")]))
 ("b"))

(test-SL-result
 ∅
 ((λ (x)
    (match x
      [("Z") ("a")]
      [("S" _) ("b")]))
  (call/cc
   (λ (k)
     ((λ (_)
        ((λ (x) (x x))
         (λ (x) (x x))))
      (k ("Z"))))))
 ("a"))

(test-SL-result
 ∅
 ((λ (x) ("S" ("S" x)))
  (letrec ([(ref k) (κ ((λ (x) ("S" x)) hole))])
    ((ref k) ("Z"))))
 ("S" ("Z")))

(test-SL-result
 ∅
 ((λ (x)
    (match ("b" x)
      [("b" x) x]))
  ("a"))
 ("a"))

(test-->>
 -->SL
 #:cycles-ok
 (term
  (∅
   /
   ((λ (t) (t t))
    (call/cc (λ (x) (call/cc x)))))))

;;; Values
(test-->> -->SL
          '(∅ / (λ (x) x))
          '(∅ / (λ (x) x)))
(test-->> -->SL
          '(∅ / ("nil"))
          '(∅ / ("nil")))
(test-->> -->SL
          '(∅ / ("S" ("0")))
          '(∅ / ("S" ("0"))))
(test-->> -->SL
          '(∅ / (ref x))
          '(∅ / (ref x)))

;;; Applications
(test-->> -->SL 
          '(∅ / ((λ (x) x) ("nil")))
          '(∅ / ("nil")))

;;; Store applications
(test-->> -->SL
          '((∅ [(ref x) ↦ (λ (x) ("nil"))])
            /
            ((ref x) ("0")))
          '((∅ [(ref x) ↦ (λ (x) ("nil"))])
            /
            ("nil")))

;;; Letrec
(test-->> -->SL
          '(∅ / (letrec ([(ref x) (λ (x) ("nil"))])
                  ("foo")))
          '((∅ [(ref x) ↦ (λ (x) ("nil"))])
            /
            ("foo")))
(test-->> -->SL
          '(∅ / (letrec ([(ref x) (λ (x) ("nil"))])
                  ((ref x) ("0"))))
          '((∅ [(ref x) ↦ (λ (x) ("nil"))])
            /
            ("nil")))

;;; match
(test-->> -->SL
          '(∅ / (match ("S" ("0"))
                  [("S" n) n]
                  [("0") ("0")]))
          '(∅ / ("0")))
(test-->> -->SL
          '(∅ / (match ("S" ("0"))
                  [("0") ("0")]
                  [("S" n) n]))
          '(∅ / ("0")))

; Store match
(test-->> -->SL
          '(∅ / (letrec ([(ref x) ("S" ("0"))])
                  (match (ref x)
                    [("S" n) n]
                    [("0") ("0")])))
          '((∅ [(ref x) ↦ ("S" ("0"))])
            /
            ("0")))

;; arith
(test-->> -->SL
          `(∅ / ,(:let 'x (num 1) 'x))
          `(∅ / ,(num 1)))
(test-SL-result ∅ ,(with-arith (num 1)) ,(num 1))
(test-SL-result ∅ ,(with-arith `((ref +) ,(num 1) ,(num 1))) ,(num 2))
(test-SL-result ∅ ,(with-arith `((ref *) ,(num 2) ,(num 2))) ,(num 4))
(test-SL-result ∅ ,(with-arith `((ref =) ,(num 2) ,(num 2))) ("#t"))
(test-SL-result ∅ ,(with-arith `((ref =) ,(num 2) ,(num 3))) ("#f"))
(test-SL-result ∅ ,(with-arith `((ref -) ,(num 3) ,(num 2))) ,(num 1))
(test-SL-result ∅ ,(with-arith (:if '("#t") (num 1) (num 2))) ,(num 1))
(test-SL-result ∅ ,(with-arith (:if '("#f") (num 1) (num 2))) ,(num 2))

;; call/cc
(test-->> -->SL
          `(∅ / (call/cc (λ (k) (k ("v")))))
          `(∅ / ("v")))
(test-->> -->SL
          `(∅ / (call/cc (λ (k) 
                           ((λ (x) ("x"))
                            (k ("v"))))))
          `(∅ / ("v")))

