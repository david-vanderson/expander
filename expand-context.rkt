#lang racket/base
(require "namespace.rkt"
         "binding.rkt")

(provide (struct-out expand-context)
         make-expand-context)

(struct expand-context (phase      ; phase currently being expanded
                        namespace  ; namespace for top-levels
                        env        ; environment for local bindings
                        only-immediate? ; #t => stop at core forms
                        ))

(define (make-expand-context ns)
  (expand-context 0
                  ns
                  empty-env
                  #f))
