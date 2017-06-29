#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "binding.rkt"
         "match.rkt"
         "core.rkt")

(provide compile
         expand-time-eval
         run-time-eval)

;; Convert an expanded syntax object to an expression that is represented
;; by a plain S-expression.
(define (compile s phase)
  (cond
   [(pair? (syntax-e s))
    (define core-sym (core-form-sym s phase))
    (case core-sym
      [(#f)
       (error "not a core form:" s)]
      [(lambda)
       (define m (match-syntax s '(lambda (id ...) body)))
       `(lambda ,(map (lambda (s) (local->symbol s phase)) (m 'id)) ,(compile (m 'body) phase))]
      [(#%app)
       (define m (match-syntax s '(#%app . rest)))
       (for/list ([s (in-list (m 'rest))])
         (compile s phase))]
      [(quote)
       (define m (match-syntax s '(quote datum)))
       `(quote ,(syntax->datum (m 'datum)))]
      [(quote-syntax)
       (define m (match-syntax s '(quote datum)))
       `(quote ,(m 'datum))]
      [else
       (error "unrecognized core form:" core-sym)])]
   [(identifier? s)
    (define b (resolve s phase))
    (cond
     [(local-binding? b)
      (define sym (key->symbol (local-binding-key b)))
      (unless sym
        (error "missing a binding after expansion:" s))
      sym]
     [(core-binding? b)
      (define sym (core-binding-sym b))
      (hash-ref core-primitives sym #f)]
     [else
      (error "not a reference to a local binding:" s)])]
   [else
    (error "bad syntax after expansion:" s)]))

;; ----------------------------------------
         
(define (local->symbol id phase)
  (define b (resolve id phase))
  (unless (local-binding? b)
    (error "bad binding:" id))
  (key->symbol (local-binding-key b)))

(define (key->symbol key)
  ;; A local-binding key is already a symbol
  key)

;; ----------------------------------------

(define expand-time-namespace (make-base-namespace))
(define run-time-namespace (make-base-namespace))

(define (expand-time-eval compiled)
  (eval compiled expand-time-namespace))

(define (run-time-eval compiled)
  (eval compiled run-time-namespace))
