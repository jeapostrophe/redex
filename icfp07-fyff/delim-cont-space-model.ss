
;; To run this model, open it in DrScheme, select the "(module ...)"
;; language, and click Run. It will take a while the first time,
;; because DrScheme will have to download the Redex package.

;; Then, at the REPL prompt, try procedures from the example section,
;; such as
;;
;;  > (show-control0-loop)

(module delim-cont-space-model mzscheme
  (require (planet "reduction-semantics.ss" ("robby" "redex.plt" 3))
           (planet "subst.ss" ("robby" "redex.plt" 3))
           (planet "gui.ss" ("robby" "redex.plt" 3))
           (lib "contract.ss")
           (lib "pretty.ss"))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Expression grammar:

  (define ls-grammar
    (language (P (D ... M))
              (D (define X V)
                 (defmacro (X X ...) M))
              (M * ; <- should only appear in `M' for `([delim-]cont M)'
                 X
                 (M M)
		 (o1 M)
		 (o2 M M)
		 V
                 (if M M M)
		 (call/cc M)
                 (prompt M)
                 (control0 X M)
                 (reset M)
                 (shift X M)
                 (X M M M ...)) ; macro application
              (V b
                 #f
                 (lambda (X) M)
                 (cont M)
                 (delim-cont M))
	      (X (variable-except lambda if
                                  call/cc cont 
                                  prompt control0 delim-cont
                                  shift reset
                                  zero? +
                                  null? list cons car cdr
                                  delay make-delay delay? delay-proc
                                  * define defmacro))
	      (b number
                 (list V ...)
                 delay-V)
              (delay-V (delay V))
              (o1 zero?
                  null? car cdr
                  make-delay delay? delay-proc)
	      (o2 + cons)
	      
	      ;; Evaluation contexts:
	      (E hole
		 (E M)
		 (V E)
		 (o1 E)
		 (o2 E M)
		 (o2 V E)
                 (if E M M)
                 (call/cc E))
	      (ME E
                  (ME M)
                  (V ME)
                  (o1 ME)
                  (o2 ME M)
                  (o2 V ME)
                  (if ME M M)
                  (call/cc ME)
                  (reset ME)
                  (prompt ME))))

  (define-syntax (define-language-predicates stx)
    (syntax-case stx ()
      [(_ id)
       (with-syntax ([? (datum->syntax-object
                         #'id
                         (string->symbol (format "~s?" (syntax-e #'id)))
                         #'id)])
         #'(define (? v) (test-match ls-grammar id v)))]
      [(_ id ...)
       #'(begin (define-language-predicates id) ...)]))
  
  (define-language-predicates P D M X V delay-V o1 o2)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Substitution:
  
  (define ls-subst
    (subst
     [(? X?) (variable)]
     [(? number?) (constant)]
     [#f (constant)]
     [`(list . ,_) (constant)]
     [`(delay ,M) (constant)]
     [`(cont ,M) (constant)]
     [`(delim-cont ,M) (constant)]
     [`(lambda (,X) ,M)
      (all-vars (list X))
      (build (lambda (X-list M) `(lambda (,(car X-list)) ,M)))
      (subterm (list X) M)]
     [`(,(and (or 'control0 'shift) o) ,X ,M)
      (all-vars (list X))
      (build (lambda (X-list M) `(,o ,(car X-list) ,M)))
      (subterm (list X) M)]
     [`(,(and (or 'call/cc 'prompt 'reset (? o1?)) o) ,M1)
      (all-vars '())
      (build (lambda (vars M1) `(,o ,M1)))
      (subterm '() M1)]
     [`(,(and (? o2?) o) ,M1 ,M2)
      (all-vars '())
      (build (lambda (vars M1 M2) `(,o ,M1 ,M2)))
      (subterm '() M1)
      (subterm '() M2)]
     [`(if ,M1 ,M2 ,M3)
      (all-vars '())
      (build (lambda (empty-list M1 M2 M3) `(if ,M1 ,M2 ,M3)))
      (subterm '() M1)
      (subterm '() M2)
      (subterm '() M3)]
     [`(,M1 ,M2)
      (all-vars '())
      (build (lambda (empty-list M1 M2) `(,M1 ,M2)))
      (subterm '() M1)
      (subterm '() M2)]
     ;; These two cases handle macro applications:
     ['()
       (all-vars '())
       (build (lambda (empty-list) '()))]
     [`(,M1 . ,M2)
      (all-vars '())
      (build (lambda (empty-list M1 M2) `(,M1 . ,M2)))
      (subterm '() M1)
      (subterm '() M2)]))

  (define (lc-replace a m)
    (let loop ([m m])
      (cond
        [(pair? m) (cons (loop (car m))
                         (loop (cdr m)))]
        [(assq m a) => cadr]
        [else m])))
        
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Reductions:

  (define :->
    (reduction-relation
     ls-grammar
     
     ;; beta
     (~~> ((lambda (X_1) M_1) V_1)
          ,(ls-subst (term X_1) (term V_1) (term M_1))
          "beta")
     
     ;; arithmetic
     (~~> (+ b_1 b_2)
          ,(+ (term b_1) (term b_2))
          "+")
     (~~> (zero? 0)
          (lambda (x) x)
          "zero?")
     (~~> (zero? V_1)
          #f
          (side-condition (not (equal? (term V_1) (term 0))))
          "non-zero")
     
     ;; lists
     (~~> (cons V_1 (list V_2 ...))
          (list V_1 V_2 ...)
          "cons")
     (~~> (car (list V_1 V_2 ...))
          V_1
          "car")
     (~~> (cdr (list V_1 V_2 ...))
          (list V_2 ...)
          "cdr")
     (~~> (null? (list))
          (lambda (x) x)
          "null?")
     (~~> (null? V_1)
          #f
          "non-null"
          (side-condition (not (equal? (term V_1) (term (list))))))

     ;; delays
     (~~> (make-delay V_1)
          (delay V_1)
          "make-delay")
     (~~> (delay-proc (delay V_1))
          V_1
          "delay-proc")
     (~~> (delay? (delay V_1))
          (lambda (x) x)
          "delay?")
     (~~> (delay? V_1)
          #f
          (side-condition (not (delay-V? (term V_1))))
          "non-delay")

     ;; if
     (~~> ((if V_1 M_1 M_2)
           . side-condition . 
           (not (eq? (term V_1) #f))) 
          M_1
          "ift")
     (~~> (if #f M_1 M_2)
          M_2
          "iff")
     
     ;; top-level definitions
     (--> (D_1 ... (define X_1 V_1) D_2 ...
               (in-hole ME_1 X_1))
          (D_1 ... (define X_1 V_1) D_2 ...
               (in-hole ME_1 V_1))
          "lookup")
     
     ;; macro
     (--> (D_1 ... (defmacro (X_1 X_2 ...) M_1) D_2 ...
               (in-hole ME_1 (X_1 M_2 ...)))
          (D_1 ... (defmacro (X_1 X_2 ...) M_1) D_2 ...
               (in-hole ME_1 ,(lc-replace (term ((X_2 M_2) ...))
                                          (term M_1))))
          "macro app")

     ;; call/cc
     (==> (in-hole E_1 (call/cc V_1))
          (in-hole E_1 (V_1 (cont (in-hole E_1 *))))
          "call/cc")
     (==> (in-hole E_1 ((cont (in-hole E_2 *)) V_1))
          (in-hole E_2 V_1)
          "continue")
     
     ;; prompt & control0
     (~~> (prompt V_1)
          V_1
          "prompt result")
     (==> (in-hole ME_1 (prompt (in-hole E_1 (control0 X_1 M_1))))
          (in-hole ME_1 (prompt ((lambda (X_1) M_1) 
                                 (delim-cont (in-hole E_1 *)))))
          "control0")
     (~~> ((delim-cont (in-hole ME_2 *)) V_1)
          (in-hole ME_2 V_1)
          "dcontinue")
     
     ;; reset & shift
     (~~> (reset V_1)
          V_1
          "reset result")
     (==> (in-hole ME_1 (reset (in-hole E_1 (shift X_1 M_1))))
          (in-hole ME_1 (reset ((lambda (X_1) M_1) 
                                (delim-cont (reset (in-hole E_1 *))))))
          "shift")
     
     where
      [(==> from to) (--> (D_1 ... from)
                          (D_1 ... to))]
      [(~~> from to) (==> (in-hole ME_1 from)
                          (in-hole ME_1 to))]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Abbreviations:
  
  (define (mk-call/cc-loop-1 call/cc)
    `(((lambda (v) ((,call/cc (lambda (x) (,call/cc x))) v))
       (,call/cc (lambda (x) (,call/cc x))))))
  
  (define (mk-call/cc-loop-2 call/cc wrap)
    `((define loop
        (lambda (v)
          (loop (,call/cc (lambda (k) (k 0))))))
      ,(wrap '(loop 0))))
  
  (define (mk-traverse prompt control0)
    `((define traverse
        (lambda (xs)
          (,prompt
            (visit xs))))
      (define visit
        (lambda (xs)
          (if (null? xs)
              (list)
              (visit (,control0 k
                       (cons (car xs) 
                             (k (cdr xs))))))))
      (traverse (list 1 2 3))))
  
  (define call/cc-via-shift
    '(lambda (f)
       (shift k (k (f (lambda (x) (shift c (k x))))))))
                  
  (define call/cc-via-control0
    '(lambda (f)
       (control0 k (k (f (lambda (x) (control0 c (k x))))))))

  (define call/cc-via-shift-trampoline
    '(lambda (f) ;; <-- called from outside
       ;; C = (trampoline (reset E[]))
       (
        ;; C = (trampoline (reset E[([] 0)])) 
        ;;  so K captures E[([] 0)]
        (shift 
         K 
         ;; C = (trampoline (reset []))
         (make-delay 
          (lambda (dummy) ;; <-- called from trampoiline
            ;; C = (trampoline [])
            (K ;; <- introduces reset and E[([] 0)]
             (lambda (dummy)
               ;; C = (trampoline (reset E[]))
               (f (lambda (x)  ;; <-- from outside
                    ;; C = (trampoline (reset E'[]))
                    (shift _
                           ;; C = (trampoline (reset []))
                           (make-delay
                            (lambda (dummy) ;; <-- called from trampoline
                              ;; C = (trampoline [])
                              (K ;; <- introduces reset and E[([] 0)]
                               (lambda (dummy)
                                 ;; C = (trampoline (reset E[]))
                                 x))))))))))))
        0)))
  
  (define trampoline
    '(lambda (v)
       ;; C = []
       (if (delay? v)
           (trampoline
            ;; C = (trampoline [])
            ((delay-proc v) 0))
           v)))

  (define (trampoline-wrap body)
    ;; Top-level to wrap original `body':
    `(trampoline (reset 
                  ;; C = (trampoline (reset []))
                  ,body)))
  
  (define shan-control0-via-shift
    `((define send
        (lambda (v)
          (lambda (mc) (if mc ((mc v) #f) v))))
      (define compose
        (lambda (c)
          (lambda (mc1)
            (if mc1
                (lambda (v)
                  (lambda (mc2)
                    ((c v) ((compose mc1) mc2))))
                c))))
      (defmacro (prompt2 e)
        ((reset (send e)) #f))
      (defmacro (control0-2 f e)
        (shift c1 
               (lambda (mc1) 
                 ((lambda (f)
                    ((reset (send e)) #f)) 
                  (lambda (x) 
                    (shift c2 
                           (lambda (mc2) 
                             ((((compose c1) mc1) x) 
                              ((compose c2) mc2)))))))))))
  
  (define kiselyov-control0-via-shift
    ;; H v1 v2 is encoded as (list 0 v1 v2)
    ;; HV v1 is encoded as (list 1 v1)
    `((define H
        (lambda (v1)
          (lambda (v2)
            (cons 0 (cons v1 (cons v2 (list)))))))
      (define HV
        (lambda (v1)
          (cons 1 (cons v1 (list)))))
      (defmacro (h-case v 
                        a b H-body
                        c HV-body)
        ((lambda (x)
           (if (zero? (car x))
               (((lambda (a)
                   (lambda (b)
                     H-body))
                 (car (cdr x)))
                (car (cdr (cdr x))))
               ((lambda (c)
                  HV-body)
                (car (cdr x)))))
         v))
      (define compose
        (lambda (f)
          (lambda (g)
            (lambda (x)
              (f (g x))))))
      (defmacro (prompt2 e)
        (h (reset (HV e))))
      (defmacro (control0-2 f e)
        (shift f- ((H ((compose h-) f-))
                   (lambda (f) e))))
      (define h
        (lambda (v)
          (h-case v
                  f x (prompt2 (x f))
                  x x)))
      (define h-
        (lambda (v)
          (h-case v
                  f x (shift g ((H ((compose ((compose h-) g)) f)) x))
                  x x)))))
      

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Examples:
  
  (define (show prog)
    (traces ls-grammar :-> prog))

  ;; The classic (let ([v (call/cc call/cc)]) 
  ;;              ((call/cc call/cc) v))
  (define (show-call/cc-loop-1)
    ;; Constant-space loop
    (show (mk-call/cc-loop-1 'call/cc)))
  
  ;; Simpler loop: (let loop ([v 0])
  ;;                 (loop (call/cc (lambda (k) 
  ;;                                  (k 0)))))
  (define (show-call/cc-loop-2)
    ;; Constant-space loop
    (show (mk-call/cc-loop-2 'call/cc (lambda (body) body))))
  
  ;; Sanity check that shift & reset work right:
  (define (show-shift-traverse)
    ;; Produces '(1 2 3)
    (show (mk-traverse 'reset 'shift)))

  ;; Sanity check that control0 & prompt work right:
  (define (show-control0-traverse)
    ;; Produces '(3 2 1)
    (show (mk-traverse 'prompt 'control0)))

  ;; Sanity check for Shan's encoding of control0 via shift:
  (define (show-shan-control0-via-shift-traverse)
    ;; Produces '(3 2 1) in 142 steps
    (show `(,@shan-control0-via-shift
            ,@(mk-traverse 'prompt2 'control0-2))))

  ;; Sanity check for Kiselyov's encoding of control0 via shift:
  (define (show-kiselyov-control0-via-shift-traverse)
    ;; Produces '(3 2 1) in 246 steps
    (show `(,@kiselyov-control0-via-shift
            ,@(mk-traverse 'prompt2 'control0-2))))

  ;; Show that the encoding of call/cc via control0
  ;; preserves space complexity on one example:
  (define (show-call/cc-loop-1-via-control0)
    ;; Constant-space loop
    (show `((define callcc ,call/cc-via-control0) 
            (prompt ,@(mk-call/cc-loop-1 'callcc)))))

  ;; Same thing, for the other example:
  (define (show-call/cc-loop-2-via-control0)
    ;; Constant-space loop
    (show `((define callcc ,call/cc-via-control0) 
            ,@(mk-call/cc-loop-2 'callcc (lambda (x) `(prompt ,x))))))

  ;; Show that the usual encoding of call/cc via shift
  ;; doesn't preserve space complexity on an example
  (define (show-call/cc-loop-2-via-shift)
    ;; **NOT** a constant-space loop
    (show `((define callcc ,call/cc-via-shift) 
            ,@(mk-call/cc-loop-2 'callcc (lambda (x) `(reset ,x))))))

  ;; Show that the revised encoding of call/cc via shift
  ;; does preserve space complexity on an example
  (define (show-call/cc-loop-2-via-shift-trampoline)
    ;; Constant-space loop
    (show `((define callcc ,call/cc-via-shift-trampoline) 
            (define trampoline ,trampoline)
            ,@(mk-call/cc-loop-2 'callcc trampoline-wrap))))
  
  ;; A loop using control0:
  (define (show-control0-loop)
    ;; Constant-space loop
    (show `((define loop
              (lambda (dummy)
                ((control0 k (k loop))
                 loop)))
            (prompt (loop 0)))))

  ;; Demonstrate that Shan's encoding of control0 via
  ;; shift doesn't preserve space complexity in the
  ;; above example:
  (define (show-shan-control0-via-shift-loop)
    ;; **NOT** a constant-space loop
    (show `(,@shan-control0-via-shift
              (define loop
                (lambda (dummy)
                  ((control0-2 k (k loop))
                   loop)))
              (prompt2 (loop 0)))))

  ;; Same thing for Kiselyov's encoding:
  (define (show-kiselyov-control0-via-shift-loop)
    ;; **NOT** a constant-space loop
    (show `(,@kiselyov-control0-via-shift
              (define loop
                (lambda (dummy)
                  ((control0-2 k (k loop))
                   loop)))
              (prompt2 (loop 0)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Exports: 
  
  ;; (not including examples, yet)
  
  (provide/contract (ls-grammar compiled-lang?)
		    (M? (any/c . -> . boolean?))
		    (X? (any/c . -> . boolean?))
		    (V? (any/c . -> . boolean?))
		    (o1? (any/c . -> . boolean?))
		    (o2? (any/c . -> . boolean?))
		    (ls-subst (X? M? M? . -> . M?))
		    (:-> reduction-relation?)))
