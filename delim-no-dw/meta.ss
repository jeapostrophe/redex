#lang scheme
(require redex
         "grammar.ss")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitution:

(define-metafunction grammar
  subst : (x e e) -> e
  [(subst (x_1 x_1 e_1)) ; shortcut
   e_1]
  [(subst (x_1 e_1 (λ (x_2 ... x_1 x_3 ...) e_2)))
   (λ (x_2 ... x_1 x_3 ...) e_2)]
  [(subst (x_1 x_2 (λ (x_3 ...) e_1))) ; shortcut; x_1 != any x_3
   (λ (x_3 ...) (subst (x_1 x_2 e_1)))]
  [(subst (x_1 e_1 (λ (x_2 ...) e_2))) ; x_1 != any x_2
   ,(term-let ([(x_new ...) (variables-not-in (term e_1) (term (x_2 ...)))])
              (term (λ (x_new ...) 
                      (subst (x_1 e_1 (subst* ((x_2 ...) (x_new ...) e_2)))))))]
  [(subst (x_1 e_1 x_1)) e_1]
  [(subst (x_1 e x_2)) x_2] ; x_1 != x_2, since previous didn't match
  [(subst (x_1 e_1 v_1)) v_1] ; all other values are atomic
  [(subst (x_1 e_1 (list v_1 ...))) (list (subst (x_1 e_1 v_1)) ...)]
  [(subst (x_1 e_1 (e_2 ...)))
   ((subst (x_1 e_1 e_2)) ...)]
  [(subst (x_1 e_1 (if e_2 e_3 e_4)))
   (if (subst (x_1 e_1 e_2)) 
       (subst (x_1 e_1 e_3))
       (subst (x_1 e_1 e_4)))]
  [(subst (x_1 e_1 (begin e_2 e_3)))
   (begin (subst (x_1 e_1 e_2)) 
          (subst (x_1 e_1 e_3)))]
  [(subst (x_1 e_1 (set! x_2 e_2)))
   (set! x_2 (subst (x_1 e_1 e_2)))]
  [(subst (x_1 e_1 (% e_2 e_3 e_4)))
   (% (subst (x_1 e_1 e_2)) 
      (subst (x_1 e_1 e_3)) 
      (subst (x_1 e_1 e_4)))]    
  [(subst (x_1 e_1 (wcm ((v_1 v_2) ...) e_2)))
   (wcm (((subst (x_1 e_1 v_1))
          (subst (x_1 e_1 v_2))) ...)
        (subst (x_1 e_1 e_2)))])

(define-metafunction grammar
  subst* : ((x ...) (e ...) e) -> e
  [(subst* (() () e_1))
   e_1]
  [(subst* ((x_1 x_2 ...) (e_1 e_2 ...) e_3))
   (subst* ((x_2 ...) (e_2 ...) (subst (x_1 e_1 e_3))))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Other meta-functions:

(define-metafunction grammar
  noPrompt : (v E) -> bool
  [(noPrompt (v_1 (% v_1 E v))) #f]
  [(noPrompt (v_1 (% v_2 E_1 v))) (noPrompt (v_1 E_1))]
  [(noPrompt (v hole)) #t]
  [(noPrompt (v_1 (v ... E_1 e ...))) (noPrompt (v_1 E_1))]
  [(noPrompt (v_1 (if E_1 e_1 e_2))) (noPrompt (v_1 E_1))]
  [(noPrompt (v_1 (begin E_1 e))) (noPrompt (v_1 E_1))]
  [(noPrompt (v_1 (set! x E_1))) (noPrompt (v_1 E_1))]
  [(noPrompt (v_1 (wcm w E_1))) (noPrompt (v_1 E_1))])

(define-metafunction grammar
  get-marks-core : (E v e) -> e
  [(get-marks-core ((in-hole hole hole) v e_2))
   e_2]
  [(get-marks-core ((wcm (name w_1 ((v_01 v_02) ... (v_1 v_3) (v_03 v_04) ...)) E_1) v_1 e_2))
   (get-marks (E_1 v_1 (cons v_3 e_2)))]
  [(get-marks-core ((wcm w_1 E_1) v_1 e_2))
   (get-marks (E_1 v_1 e_2))
   (side-condition (term (notInDom (v_1 w_1))))]
  [(get-marks-core ((v ... E_1 e ...) v_1 e_2))
   (get-marks (E_1 v_1 e_2))]
  [(get-marks-core ((begin E_1 e) v_1 e_2))
   (get-marks (E_1 v_1 e_2))]
  [(get-marks-core ((% v_01 E_1 v_02) v_1 e_2))
   (get-marks (E_1 v_1 e_2))])

(define-metafunction grammar
  get-marks : (E v e) -> e
  [(get-marks ((if E_1 e_01 e_02) v_1 e_2))
   (get-marks (E_1 v_1 e_2))]
  [(get-marks ((set! x E_1) v_1 e_2))
   (get-marks (E_1 v_1 e_2))]
  [(get-marks (E_1 v_1 e_2))
   (get-marks-core (E_1 v_1 e_2))])

(define-metafunction grammar
  expose-wcm : (e) -> e
  [(expose-wcm (e_1))
   e_1
   (side-condition (term (noMatchWCM (e_1 (wcm w e)))))]
  [(expose-wcm ((wcm () e_1)))
   e_1]
  [(expose-wcm ((wcm ((v_1 v_2) (v_3 v_4) ...) e_1)))
   (call/cm v_1 v_2 (λ () (expose-wcm ((wcm ((v_3 v_4) ...) e_1)))))])

(define-metafunction grammar
  nonWCM : E -> bool
  [(nonWCM (in-hole E (wcm w hole))) #f]
  [(nonWCM any) #t])

;; The rest are helpers that are typeset specially in the paper

(define-metafunction grammar
  noMatch : (E any any) -> bool
  [(noMatch (E_1 any_1 (% v_1 any_2 any_3)))
   (noPrompt (v_1 E_1))]
  [(noMatch (E_1 any_1 (wcm any_2 any_3)))
   (nonWCM E_1)])

(define-metafunction grammar
  noMatchWCM : (e any) -> bool
  [(noMatchWCM ((wcm w e_1) any)) #f]
  [(noMatchWCM any) #t])

(define-metafunction grammar
  notIn : (v (v ...)) -> bool
  [(notIn (v_1 (v_2 ...)))
   ,(not (member (term v_1) (term (v_2 ...))))])

(define-metafunction grammar
  notInDom : (v ((v v) ...)) -> bool
  [(notInDom (v_1 ((v_2  v_3) ...)))
   (notIn (v_1 (v_2 ...)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide subst*
         get-marks
         expose-wcm
         noMatch
         notIn)