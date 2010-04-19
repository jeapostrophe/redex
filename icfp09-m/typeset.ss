#lang scheme
(require redex/pict
         "sl.ss"
         "tl.ss"
         "cmt.ss")

;; SL
(render-language sl-grammar)
(render-reduction-relation -->_sl) 

;; TL
(render-language tl-grammar)
(render-reduction-relation -->_tl)
(render-metafunction get-marks)

;; CMT
(render-language sl-grammar+cmt)
(render-metafunctions CMT-v CMT-w CMT-a CMT-l CMT-r CMT-EE CMT-e)

