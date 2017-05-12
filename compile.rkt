#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "namespace.rkt"
         "match.rkt")

(provide compile
         expand-time-eval
         run-time-eval)

;; Convert an expanded syntax object to an expression that is represented
;; by a plain S-expression.
(define (compile s
                 phase
                 [ns (current-namespace)]) ; compile-time namespace
  (let ([compile (lambda (s) (compile s phase ns))])
    (cond
     [(pair? (syntax-e s))
      ;; fully expanded pairs are all core forms, including #%app, #%datum, etc.
      (define core-sym (syntax-e (car (syntax-e s))))
      (case core-sym
        [(lambda)
         (define m (match-syntax s '(lambda formals body)))
         `(lambda ,@(compile-lambda (m 'formals) (m 'body) phase ns))]
        [(case-lambda)
         (define m (match-syntax s '(case-lambda [formals body] ...)))
         `(case-lambda ,@(for/list ([formals (in-list (m 'formals))]
                               [body (in-list (m 'body))])
                      (compile-lambda formals body phase ns)))]
        [(#%app)
         (define m (match-syntax s '(#%app . rest)))
         (for/list ([s (in-list (m 'rest))])
           (compile s))]
        [(if)
         (define m (match-syntax s '(if tst thn els)))
         `(if
           ,(compile (m 'tst))
           ,(compile (m 'thn))
           ,(compile (m 'els)))]
        [(with-continuation-mark)
         (define m (match-syntax s '(with-continuation-mark key val body)))
         `(with-continuation-mark
           ,(compile (m 'key))
           ,(compile (m 'val))
           ,(compile (m 'body)))]
        [(begin begin0)
         (define m (match-syntax s '(begin e ...+)))
         `(,core-sym ,@(for/list ([e (in-list (m 'e))])
                                      (compile e)))]
        [(set!)
         (define m (match-syntax s '(set! id rhs)))
         `(set!
           ,(compile (m 'id))
           ,(compile (m 'rhs)))]
        [(let-values letrec-values)
         (compile-let core-sym s phase ns)]
        [(quote)
         (define m (match-syntax s '(quote datum)))
         `(quote ,(syntax->datum (m 'datum)))]
        [(quote-syntax)
         (define m (match-syntax s '(quote datum)))
         `(quote ,(m 'datum))]
        [else
         (error "unrecognized core form:" core-sym)])]
     [(identifier? s)
      (define b (resolve s phase #t))
      (case (bind-type b)
        [(var prim)
         (bind-val b)] 
        [else
         (error "not a reference to a local binding or primitive:" s)])]
;      (cond
;       [(local-binding? b)
;        (define sym (key->symbol (local-binding-key b)))
;        (unless sym
;          (error "missing a binding after expansion:" s))
;        sym]
;       [(top-level-binding? b)
;        (define sym (top-level-binding-sym b))
;        (namespace-get-variable ns sym #f)]
;       [else
;        (error "not a reference to a local binding:" s)])]
     [else
      (error "bad syntax after expansion:" s)])))

(define (compile-lambda formals body phase ns)
  (define gen-formals
    (let loop ([formals formals])
      (cond
       [(identifier? formals) (bind-val (resolve formals phase #t))]
       [(syntax? formals) (loop (syntax-e formals))]
       [(pair? formals) (cons (loop (car formals))
                              (loop (cdr formals)))]
       [else null])))
  `(,gen-formals ,(compile body phase ns)))

(define (compile-let core-sym s phase ns)
  (define rec? (eq? core-sym 'letrec-values))
  (define m (match-syntax s '(let-values ([(id ...) rhs] ...) body)))
  (define symss (for/list ([ids (in-list (m 'id))])
                  (for/list ([id (in-list ids)])
                    (bind-val (resolve id phase #t)))))
  `(,core-sym ,(for/list ([syms (in-list symss)]
                          [rhs (in-list (m 'rhs))])
                 `[,syms ,(compile rhs phase ns)])
    ,(compile (m 'body) phase ns)))


;; ----------------------------------------

(define expand-time-namespace (make-base-namespace))
;(define (add-expand-time! sym val)
;  (namespace-set-variable-value! sym val #t expand-time-namespace))
;
;(add-expand-time! 'current-namespace current-namespace)
;(add-expand-time! 'namespace-get-variable namespace-get-variable)
;(add-expand-time! 'syntax-shift-phase-level syntax-shift-phase-level)

(define run-time-namespace (make-base-namespace))
;(define (add-run-time! sym val)
;  (namespace-set-variable-value! sym val #t run-time-namespace))
;
;(add-run-time! 'current-namespace current-namespace)
;(add-run-time! 'namespace-get-variable namespace-get-variable)
;(add-run-time! 'syntax-shift-phase-level syntax-shift-phase-level)

(define (expand-time-eval compiled)
  (eval compiled expand-time-namespace))

(define (run-time-eval compiled)
  (eval compiled run-time-namespace))
