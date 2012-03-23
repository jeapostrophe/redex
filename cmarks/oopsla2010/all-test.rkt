#lang racket/base
(define mods
  '("sl-tests.rkt"
    "tl-tests.rkt"
    "cmt-tests.rkt"
    "sl-prop.rkt"
    "tl-prop.rkt"
    "cmt-prop.rkt"))
(for ([m mods])
  (printf "~a\n" m)
  (dynamic-require m #f))
