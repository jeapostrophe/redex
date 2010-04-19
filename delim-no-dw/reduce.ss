#lang scheme
(require redex
         "grammar.ss"
         "meta.ss")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reductions:

(define :->
  (reduction-relation
   grammar
   
   ;; beta
   (~~> ((λ (x_1 ...) e_1) v_1 ...)
        (subst* ((x_1 ...) (v_1 ...) e_1))
        "beta")
   
   ;; arithmetic
   (~~> (+ n_1 n_2)
        ,(+ (term n_1) (term n_2))
        "+")
   (~~> (zero? 0)
        #t
        "zero?")
   (~~> (zero? v_1)
        #f
        (side-condition (not (zero? (term v_1))))
        "non-zero")
   
   ;; lists
   (~~> (cons v_1 (list v_2 ...))
        (list v_1 v_2 ...)
        "cons")
   (~~> (first (list v_1 v_2 ...))
        v_1
        "first")
   (~~> (rest (list v_1 v_2 ...))
        (list v_2 ...)
        "rest")
   
   ;; printing
   (--> (<> s_1 [o_1 ...] (in-hole E_1 (print o_2)))
        (<> s_1 [o_1 ... o_2] (in-hole E_1 #f))
        "print")
   
   ;; if
   (~~> (if #t e_1 e_2)
        e_1
        "ift")
   (~~> (if #f e_1 e_2)
        e_2
        "iff")
   
   ;; begin
   (~~> (begin v e_1)
        e_1
        "begin-v")
   
   ;; set! and lookup
   (--> (<> ([x_1 v_1] ... [x_2 v_2] [x_3 v_3] ...) [o_1 ...] (in-hole E_1 (set! x_2 v_4)))
        (<> ([x_1 v_1] ... [x_2 v_4] [x_3 v_3] ...) [o_1 ...] (in-hole E_1 #f))
        "assign")
   (--> (<> ([x_1 v_1] ... [x_2 v_2] [x_3 v_3] ...) [o_1 ...] (in-hole E_1 x_2))
        (<> ([x_1 v_1] ... [x_2 v_2] [x_3 v_3] ...) [o_1 ...] (in-hole E_1 v_2))
        "lookup")
   
   ;; prompt
   ;;  When we get a value, drop the prompt.
   (~~> (% v_1 v_2 v_3)
        v_2
        "prompt-v")
   
   ;; call/cc
   ;;  Capture; the context E_2 must not include a prompt with the same tag,
   ;;  and we don't want immediate marks.
   (~~> (% v_2 (in-hole E_2 (wcm w_1 (call/cc v_1 v_2))) v_3)
        (% v_2 (in-hole E_2 (wcm w_1 (v_1 (cont v_2 E_2)))) v_3)
        (side-condition (term (noMatch (E_2 E (% v_2 E v)))))
        "call/cc")
   ;;  Invoke a continuation
   (~~> (% v_1 (in-hole E_3 ((cont v_1 (in-hole E_4 hole)) v_2)) v_3)
        (% v_1 (in-hole E_4 v_2) v_3)
        (side-condition (term (noMatch (E_3 E (% v_1 E v)))))
        "cont")
   
   ;; abort
   ;;  Like continuation invocation:
   (~~> (% v_1 (in-hole E_2 (abort v_1 v_2)) v_3)
        (v_3 v_2)
        (side-condition (term (noMatch (E_2 E (% v_1 E v)))))
        "abort")
   
   ;; composable continuation
   ;;  Capture up to the relevant prompt, not including immediate marks:
   (~~> (% v_2 (in-hole E_2 (wcm w_1 (call/comp v_1 v_2))) v_3)
        (% v_2 (in-hole E_2 (wcm w_1 (v_1 (comp E_2)))) v_3)
        (side-condition (term (noMatch (E_2 E (% v_2 E v)))))
        "call/comp")
   ;;  On invocation, we want to splice leading `wcm's with any marks
   ;;  at the invocation context. We do that by convertings the leading
   ;;  `wcm's back to `call/cm', so they get spliced as usual
   ;;  for evaluating `call/cm' (see below).
   (~~> ((comp (in-hole E_1 hole)) v_1)
        (expose-wcm ((in-hole E_1 v_1)))
        "comp")
   
   ;; continuation marks
   ;;  Introduce a `wcm' when needed for certain primitives:
   (-+> (in-hole E_1 (u_1 v_1 ...))
        (in-hole E_1 (wcm () (u_1 v_1 ...)))
        (side-condition (term (noMatch (E_1 E (wcm w hole)))))
        "wcm-intro")
   ;;  When we get a value, discard marks:
   (~~> (wcm w v_1)
        v_1
        "wcm-v")
   
   ;;  When `call/cm' uses the same key as a wrapping
   ;;  mark, then replace the old value.
   (~~> (wcm ((v_1 v_2) ... (v_3 v_4) (v_5 v_6) ...) 
             (call/cm v_3 v_7 (λ () e_1)))
        (wcm ((v_1 v_2) ... (v_3 v_7) (v_5 v_6) ...) e_1)
        "wcm-set")
   ;;  When `call/cm' uses a different key than any wrapping
   ;;  mark, then add a new mark.
   (~~> (wcm ((v_1 v_2) ...) (call/cm v_3 v_4 (λ () e_1)))
        (wcm ((v_1 v_2) ... (v_3 v_4)) e_1)
        (side-condition (term (notIn (v_3 (v_1 ...)))))
        "wcm-add")
   ;;  To get the current mark value for mark key, search
   ;;  the current context (using `get-marks'), using only
   ;;  the part of the continuation up to a prompt with the
   ;;  given tag.
   (~~> (% v_2 (in-hole E_2 (current-marks v_1 v_2)) v_3)
        (% v_2 (in-hole E_2 (get-marks (E_2 v_1 (list)))) v_3)
        (side-condition (term (noMatch (E_2 E (% v_2 E v)))))
        "marks")
   
   with
   ;; -+> is evaluation independent of the store and output:
   [(--> (<> s_1 [o_1 ...] from) (<> s_1 [o_1 ...] to))
    (-+> from to)]
   ;; ~~> is evaluation in any E:
   [(-+> (in-hole E_1 from)
         (in-hole E_1 to))
    (~~> from to)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide :->)