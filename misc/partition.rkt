#lang racket
(require tests/eli-tester)

;; split-at : (A -> bool) (list A) -> (list A) (list A)
(define (split-at? ? l)
  (if (empty? l)
      (values empty empty)
      (cond
       [(? (first l))
        (values empty l)]
       [else
        (define-values (before after) (split-at? ? (rest l)))
        (values (cons (first l) before)
                after)])))

(test
 (split-at? even? (list 1 3 5 4 3 5 7))
 =>
 (values (list 1 3 5)
         (list 4 3 5 7)))

;; partition-alists : alist any -> (values alist any alist)
(define (partition-alists-no-match l key)
  (define-values (before after) 
    (split-at? (compose
                (curry equal? key)
                car)
               l))  
  (if (empty? after)
      (values before #f #f)
      (values before
              (cdr (first after))
              (rest after))))

(require unstable/match)
(define (partition-alists l key)
  (match l
         [(list before ... (cons (== key) val) after ...)
          (values before val after)]
         [_
          (values l #f #f)]))

(test
 (partition-alists '([r1 -> x] [r2 -> y] [r3 -> z])
                   'r1)
 =>
 (values '()
         '(-> x)
         '([r2 -> y] [r3 -> z]))

 (partition-alists '([r1 -> x] [r2 -> y] [r3 -> z])
                   'r2)
 =>
 (values '([r1 -> x])
         '(-> y)
         '([r3 -> z]))

 (partition-alists '([r1 -> x] [r2 -> y] [r3 -> z])
                   'r4)
 =>
 (values '([r1 -> x] [r2 -> y] [r3 -> z])
         #f
         #f))
