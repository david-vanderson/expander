#lang racket/base

(provide (struct-out expand-context)
         make-expand-context)

(struct expand-context (coret           ; see coret in core.rkt
                        phase           ; integer
                        namespace       ; namespace for top-levels
                        only-immediate? ; #t => stop at core forms for definition contexts
                        record-tips     ; when in definition context,
                        ; points to a box containing a list of tips that need updating
                        ))

(define (make-expand-context ns coret)
  (expand-context coret 0 ns #f #f))
