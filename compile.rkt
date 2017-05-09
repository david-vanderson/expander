#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt")

(provide compile
         expand-time-eval
         run-time-eval)

;; Convert an expanded syntax object to an expression that is represented
;; by a plain S-expression.
(define (compile s (phase 0))
  (cond
   [(pair? (syntax-e s))
    ;; fully expanded pairs are all core forms (applications are now #%app)
    (case (syntax-e (car (syntax-e s)))
      [(lambda)
       (define m (match-syntax s '(lambda (id ...) body)))
       `(lambda ,(map (lambda (id) (bind-val (resolve id phase #t))) (m 'id)) ,(compile (m 'body) phase))]
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
       (error "unrecognized core form:" (car (syntax-e s)))])]
   [(identifier? s)
    (define b (resolve s phase #t))
    (case (bind-type b)
      [(var prim)
       (bind-val b)]
      [else
       (error "not a reference to a local binding or primitive:" s)])]
   [else
    (error "bad syntax after expansion:" s)]))


(define expand-time-namespace (make-base-namespace))
(define run-time-namespace (make-base-namespace))

(define (expand-time-eval compiled)
  (eval compiled expand-time-namespace))

(define (run-time-eval compiled)
  (eval compiled run-time-namespace))

