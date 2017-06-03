#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "namespace.rkt"
         "core.rkt"
         "expand-context.rkt"
         (rename-in "expand.rkt" [expand expand-in-context])
         (rename-in "compile.rkt" [compile compile-in-namespace]))


(define (namespace-syntax-introduce s)
  (introduce s 0 coreb))
 
(define (expand s)
  (expand-in-context s (make-expand-context (current-namespace) coreb)))

(struct compiled-expression (s-expr)
        #:property prop:custom-write
        (lambda (c port mode)
          (fprintf port "#<compiled-expression:~.s>" (compiled-expression-s-expr c))))

(define (compile s [ns (current-namespace)])
  (compiled-expression (compile-in-namespace s 0 ns)))

(define (eval s [ns (current-namespace)])
  (if (compiled-expression? s)
      (run-time-eval (compiled-expression-s-expr s))
      (run-time-eval (compile-in-namespace
                      (expand-in-context
                       (namespace-syntax-introduce
                        (datum->syntax #f s))
                       (make-expand-context ns coreb))
                      0
                      ns))))

;; ----------------------------------------

;; Externally visible functions:
(provide syntax? syntax-e
         identifier?
         datum->syntax syntax->datum
         syntax-property
         
         bound-identifier=?
         free-identifier=?
         
         current-namespace
         
         namespace-syntax-introduce
         
         expand
         compile
         eval
         
         compiled-expression?)
