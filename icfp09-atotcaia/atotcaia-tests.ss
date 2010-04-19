#lang scheme
(require redex
         tests/eli-tester
         "atotcaia-search.ss")

(test
 (term (Γ/append · ((· u : (var h)) (var B) : ((var m) → (var a)))))
 
 ; pg 330 (right bottom)
 (true? 
  (term (coerce ((· ftoi : Float → Int)
                 ((· f : (Int → Int)) x : Float)
                 ⊢ b b
                 (f x)
                 ~~>
                 (f (ftoi x))
                 :
                 Int))))
 
 ; pg 331 (left top)
 ; XXX The paper incorrectly synthesizes these environments on the left from the previous ones
 (true?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 ((plus x) x)
                 ~~>
                 (((ptoi plus) (ftoi x)) (ftoi x))
                 :
                 Int))))
 
 (true?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 ((plus x) x)
                 ~~>
                 (((ptof plus) x) x)
                 :
                 Float))))
 
 ; With casts
 (true?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 (((plus x) x) : Int)
                 ~~>
                 (((ptoi plus) (ftoi x)) (ftoi x))
                 :
                 Int))))
 
 (true?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 (((plus x) x) : Float)
                 ~~>
                 (((ptof plus) x) x)
                 :
                 Float))))
 
 ; Casts rule out the other
 (false?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 (((plus x) x) : Float)
                 ~~>
                 (((ptoi plus) (ftoi x)) (ftoi x))
                 :
                 Int))))
 
 (false?
  (term (coerce ((((· ptof : P → (Float → (Float → Float)))
                   ptoi : P → (Int → (Int → Int)))
                  ftoi : Float → Int)
                 (((· plus : P) f : (Int → Int)) x : Float)
                 ⊢ b b
                 (((plus x) x) : Int)
                 ~~>
                 (((ptof plus) x) x)
                 :
                 Float))))
 
 ; pg 333
 (true?
  (term
   (generate (((· f : A → B) g : B → C)
              ⊢
              A
              <I r
              C
              ~~>
              (((id C) ◦ g) ◦ f)))))
 
 ; pg 333, Figure 4
 (true?
  (term
   (coerce (((((· conX : X → Int) absX : Int → X)
              conY : Y → X) absY : X → Y)
            (((· one : Int) y : Y) f : (X → (X → X)))
            ⊢ r r
            ((f y) one)
            ~~>
            ((f (((id X) ◦ conY) y))
             (((id X) ◦ absX) one))
            :
            X))))
 )


; pg 336, Figure 7
(define Fig7-Σ 
  (term
   ((((((((· Bo : Bool → Dyn) Bn : Dyn → Bool)
         I : Int → Dyn) In : Dyn → Int)
       F : (Dyn → Dyn) → Dyn) Fn : Dyn → (Dyn → Dyn))
     P : (Dyn × Dyn) → Dyn) Pn : Dyn → (Dyn × Dyn))))

; XXX Both wrong in the paper
(test
 (true? (term (coerce (,Fig7-Σ 
                       (· one : Int)
                       ⊢ r s
                       ((λ x : Dyn x) one)
                       ~~>
                       ((λ x : Dyn x) (((id Dyn) ◦ I) one))
                       :
                       Dyn))))
 
 (true? (term (coerce (,Fig7-Σ 
                       ((· one : Int) true : Bool)
                       ⊢ r s
                       (one true)
                       ~~>
                       (((((id (Dyn → Dyn)) ◦ Fn) ◦ I) one) (((id Dyn) ◦ Bo) true))
                       :
                       Dyn)))))

; I had to enumerate to figure out the right one:
#;(for*/list ([one (in-list (list #t #f))]
            [Fn (in-list (list #t #f))]
            [I (in-list (list #t #f))]
            [Bo (in-list (list #t #f))])
  (define (insert do-it t x)
    (if do-it
        `((id ,t) ◦ ,x)
        x))
  (list one Fn I Bo
        (true? (term (coerce (,Fig7-Σ 
                              ((· one : Int) true : Bool)
                              ⊢ r s
                              (one true)
                              ~~>
                              ((,(insert one '(Dyn → Dyn) (term (,(insert Fn '(Dyn → Dyn) 'Fn) ◦ ,(insert I 'Dyn 'I)))) one) (,(insert Bo 'Dyn 'Bo) true))
                              :
                              Dyn))))))

(local [(define Σ
          (term ((((· conX : X → Int) absX : Int → X)
                  conY : Y → X) absY : X → Y)))]
  (test
   (Reachable Σ 'X 'Y)
   (Reachable Σ 'X 'X)
   (Reachable Σ 'X 'Int)
   (Reachable Σ 'Y 'Y)
   (Reachable Σ 'Y 'X)
   (Reachable Σ 'Y 'Int)
   (Reachable Σ 'Int 'Y)
   (Reachable Σ 'Int 'X)
   (Reachable Σ 'Int 'Int)))

(test
 (BaseCoercions (term ·))
 (BaseCoercions (term (· x : X → Y)))
 (BaseCoercions (term (· x : X → (Y → Z))))
 (BaseCoercions (term (· x : (X → Y) → Z))) => #f
 (BaseCoercions (term ((· x : X → Y) x : X → Y)))
 (BaseCoercions (term ((· x : X → Y) x : X → (Y → Z))))
 (BaseCoercions (term ((· x : X → Y) x : (X → Y) → Z))) => #f
 (BaseCoercions (term ((· x : (X → Y) → Z) x : X → Y))) => #f
 (BaseCoercions (term ((· x : (X → Y) → Z) x : X → (Y → Z)))) => #f
 (BaseCoercions (term ((· x : (X → Y) → Z) x : (X → Y) → Z))) => #f)
        
; pg 337 (poorly specified in paper)
(define p337-ex
  (term
  (coerce (((· lazy : (forall (a) ((Unit → a) → (Lazy a))))
            force : (forall (a) ((Lazy a) → a)))
           ((· + : (Int → (Int → Int)))
            one : Int)
           ⊢ p s ;XXX q?
           ((λ y : (Lazy Int) ((+ y) one)) (λ x : Unit e))
           ~~>
           ((λ y : (Lazy Int) ((+ ((inst force (Int)) y)) one)) (lazy (λ x : Unit e)))
           :
           Int))))
(test
 (true? p337-ex))
 
#;(step-it p337-ex)