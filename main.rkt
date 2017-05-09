#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "core.rkt"
         (rename-in "expand.rkt" [expand expand-in-phase])
         "compile.rkt")


(define (expand s)
  (expand-in-phase s 0))
 
(define (eval s)
  ;; Assume that `s` is compiled
  (run-time-eval s))

;; ----------------------------------------

;; Externally visible functions:
(provide syntax? syntax-e
         identifier?
         datum->syntax syntax->datum
         syntax-property
         
         bound-identifier=?
         free-identifier=?
         namespace-syntax-introduce
         
         expand
         compile
         eval)
