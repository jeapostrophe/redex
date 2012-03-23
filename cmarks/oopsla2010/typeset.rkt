#lang racket
(require racket/runtime-path
         redex/reduction-semantics
         redex/pict
         "sl.rkt"
         "tl.rkt"
         "cmt.rkt"
         (for-syntax "cmt.rkt"))

(define-runtime-path typeset "typeset")

;; SL
(render-language sl-grammar
                 (build-path typeset "sl-grammar.eps")
                 #:nts '(e l a w v Sigma E))
(render-reduction-relation -->_sl
                           (build-path typeset "sl-red.eps")) 

;; TL
(render-language tl-grammar
                 (build-path typeset "tl-grammar.eps")
                 #:nts '(e l a w v Sigma E F))
(render-reduction-relation -->_tl
                           (build-path typeset "tl-red.eps"))
(render-metafunctions get-marks-tl wcm-merge wcm-replace
                      #:file (build-path typeset "tl-meta.eps"))

(define-extended-language tl-grammar-marks
  tl-grammar
  [marks ("nil")
         ("cons" mark-set marks)]
  [mark-set ("marks" maybe-mark ...)]
  [maybe-mark ("none")
              ("some" v)])

(render-language tl-grammar-marks
                 (build-path typeset "tl-marks.eps"))

;; CMT
(render-language sl-grammar+cmt
                 (build-path typeset "slcmt-grammar.eps"))
(render-metafunctions sl-context->marks 
                      #:file (build-path typeset "cmt-meta-helper.eps"))
(render-metafunctions CMT-v CMT-w CMT-a CMT-l CMT-r CMT-EE CMT-e
                      #:file (build-path typeset "cmt-meta.eps"))

(render-term tl-grammar 
             (letrec
                 (["resume"
                   (λ (l v)
                     (match l
                       [("nil") => v]
                       [("cons" k*cm l) 
                        => (match k*cm
                             [("marks" mk)
                              =>
                              (match mk
                                [("some" k)
                                 => (k (wcm ([("square") k]) ((! "resume") l v)))]
                                [("none")
                                 => (abort ("not marks"))])])]))]
                  ["call/cc"
                   (λ (f)
                     ((λ (is-safe?)
                        (match is-safe?
                          [("#t") =>
                                  ((λ (k)
                                     (f k))
                                   ((λ (m)
                                      (λ (x) (abort ((! "resume") m x))))
                                    (c-c-m ("square"))))]
                          [("#f") => (abort ("unsafe context"))]))
                      ((! "all-safe?")
                       (c-c-m ("safe-call?")))))])
               ...)
             (build-path typeset "stdlib.eps"))
