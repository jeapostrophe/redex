#lang scheme
(require redex
         redex/gui
         "grammar.ss"
         "meta.ss"
         "reduce.ss")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abbreviations:

;; The classic (let ([v (call/cc call/cc)]) 
;;              ((call/cc call/cc) v))
(define call/cc-loop
  `(<>
    () []
    (% 0
       ((λ (v) ((call/cc (λ (x) (call/cc x 0)) 0) v))
        (call/cc (λ (x) (call/cc x 0)) 0))
       (λ (x) x))))

(define (show prog)
  (stepper :-> prog))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
(define (test desc expr result)
  (printf "~s:\n~s\n" desc expr)
  (let ([r (car (apply-reduction-relation* :-> expr))])
    (printf "=> ~s\n\n" r)
    (unless (equal? r result)
      (error 'test "expected ~s" result))))

;; Basic ----------------------------------------

(define (basic-tests)
  (test "abort"
        '(<>
          () []
          (%
           0             
           (+ 10 (abort 0 7))
           (λ (x) (+ x 1))))
        '(<>
          () []
          8))
  (test "abort inner"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               1         
               (abort 1 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          18))
  (test "abort outer"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               1
               (abort 0 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          9))
  (test "abort inner with same tag"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               0
               (abort 0 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          18))
  (test "abort handler in tail position"
        '(<>
          () []
          (%
           0
           (call/cm
            100 1
            (λ ()
              (%
               1
               (abort 1 (λ ()
                          (call/cm
                           100 2
                           (λ ()
                             (current-marks 100 0)))))
               (λ (f)
                 (f)))))
           (λ (x) x)))
        '(<>
          () []
          (list 2)))
  (test "composable captures continuation marks"
        '(<>
          () []
          (%
           100
           ((λ (k) (k (λ (v) (current-marks 0 100)))) 
            (% 0 
               (call/cm 0 100 
                        (λ ()
                          ((call/comp (λ (k) (λ (v) k)) 0)
                           99)) )
               (λ (x) x)))
           (λ (x) x)))
        '(<> () [] (list 100)))
  (test "continuation marks wrapping % not captured"
        '(<>
          () []
          (%
           101
           ((λ (k) (k (λ (v) (current-marks 0 101)))) 
            (call/cm 0 100 
                     (λ ()
                       (% 0 
                          ((call/comp (λ (k) (λ (v) k)) 0)
                           99)
                          (λ (x) x)))))
           (λ (x) x)))
        '(<> () [] (list)))
  (test "visible marks restricted by prompt tag"
        '(<>
          () []
          (% 101
             (call/cm 0 100
                      (λ ()
                        (% 102
                           (call/cm 0 99
                                    (λ () 
                                      (current-marks 0 102)))
                           (λ (x) x))))
             (λ (x) x)))
        '(<> () [] (list 99)))
  (test "visible marks not restricted by other prompt tags"
        '(<>
          () []
          (% 101
             (call/cm 0 100
                      (λ ()
                        (% 102
                           (call/cm 0 99
                                    (λ () 
                                      (current-marks 0 101)))
                           (λ (x) x))))
             (λ (x) x)))
        '(<> () [] (list 99 100)))
  (test "getting marks fails if there's no prompt with the given tag"
        '(<>
          () []
          (% 101
             (call/cm 0 100
                      (λ ()
                        (current-marks 0 102)))
             (λ (x) x)))
        '(<> () [] (% 101 (wcm ((0 100)) (current-marks 0 102)) (λ (x) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; composability

(define (cont-tests)
  (test "captured under new %"
        '(<>
          ([retry #f])
          []
          (begin
            (%
             0
             (+ 18
                (call/cc
                 (λ (k)
                   (begin
                     (set! retry k)
                     17))
                 0))
             (λ (x) x))
            ((λ (y)
               (begin
                 (set! retry #f)
                 y))
             (+ 1 (%
                   0
                   (retry 10)
                   (λ (x) x))))))
        '(<>
          ([retry #f])
          []
          29))               
  (test "catch in composed"
        '(<>
          () []
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (%
                  0
                  (k2 (list 89))
                  (λ (x) x)))
               (%
                0
                (k (λ ()
                     (first (call/cc (λ (k2)
                                       (cons k2 (list)))
                                     0))))
                (λ (x) x))))
            (%
             0
             ((call/cc (λ (k) (λ () k))
                       0))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          () []
          89))
  (test "simple composable"
        '(<>
          [] ()
          ((λ (k)
             (k (λ () 8)))
           (%
            0
            ((call/comp
              (λ (k) (λ () k))
              0))
            (λ (x) x))))
        '(<> [] () 8))
  (test "composable doesn't introduce %"
        '(<>
          [] ()
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (if (first (rest k2))
                     ((first k2) (list 10 #f))
                     (first k2)))
               (k (λ ()
                    (call/cc (λ (k2) 
                               (cons k2 (list #t)))
                             0)))))
            (%
             0
             ((call/comp
               (λ (k) (λ () k))
               0))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          [] ()
          10))  
  (test "loop"
        '(<>
          ([counter (list 4 3 2 1 0)])
          []
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (if (first (rest k2))
                     ((first k2) (λ () 
                                   (if (zero? (first counter))
                                       (list 10 #f)
                                       (begin
                                         (set! counter (rest counter))
                                         ((call/cc (λ (k) (λ () 
                                                            (cons k (list #t))))
                                                   0))))))
                     (first k2)))
               (%
                1
                (k (λ ()
                     ((call/cc (λ (k) (λ () 
                                        (cons k (list #t))))
                               0))))
                (λ (x) x))))
            (%
             1
             ((call/cc (λ (k) (λ () k))
                       1))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          ([counter (list 0)])
          []
          10))
  (void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Run

(begin
  (basic-tests)
  (cont-tests))