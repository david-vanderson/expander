#lang racket/base

(provide (struct-out expand-context)
         make-expand-context)

(struct expand-context (coret           ; see coret in core.rkt
                        phase           ; integer
                        namespace       ; namespace for top-levels

                        ; hasheq mapping phase -> list of tips
                        ; if phase is in the mapping it means we are expanding
                        ; a definition context in that phase, so freeze and thaw
                        ; need to deal with that and add new tips to the list
                        defctx-tips
                        ))

(define (make-expand-context ns coret)
  (expand-context coret 0 ns (make-hasheq)))
