#lang racket/base
(require "binding.rkt")

(provide (struct-out expand-context)
         make-expand-context
         current-expand-context)

(struct expand-context (context    ; 'expression, 'module, or 'top-level
                        phase      ; current expansion phase
                        namespace  ; namespace for modules and top-levels
                        env        ; environment for local bindings
                        only-immediate? ; #t => stop at core forms
                        module-begin-k ; expander for `#%module-being` in a 'module-begin context
                        ))

(define (make-expand-context ns)
  (expand-context 'top-level
                  0
                  ns
                  empty-env
                  #f   ; only-immediate?
                  #f)) ; module-begin-k

(define current-expand-context (make-parameter #f))
