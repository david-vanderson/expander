#lang racket/base

(provide (struct-out expand-context)
         make-expand-context)

(struct expand-context (coreb        ; see coreb in core.rkt
                        phase        ; integer
                        namespace    ; namespace for top-levels
                        only-immediate?  ; expand only to core forms?
                        ))

(define (make-expand-context ns coreb)
  (expand-context coreb 0 ns #f))
