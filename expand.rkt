#lang racket/base
(require racket/set
         racket/unit
         "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "binding.rkt"
         "compile.rkt"
         "core.rkt")

(provide expand
         lookup
         eval-for-syntax-binding
         rebuild)

;; ----------------------------------------

;; Main expander loop:
(define (expand s env phase)
  (cond
   [(identifier? s)
    (expand-identifier s env phase)]
   [(and (pair? (syntax-e s))
         (identifier? (car (syntax-e s))))
    (expand-id-application-form s env phase)]
   [(or (pair? (syntax-e s))
        (null? (syntax-e s)))
    ;; An "application" form that doesn't start with an identifier
    (expand-app s env phase)]
   [else
    ;; Anything other than an identifier or parens is implicitly quoted
    (rebuild s (list (core-literal 'quote phase) s))]))

;; An identifier by itself:
(define (expand-identifier s env phase)
  (define binding (resolve s phase))
  (cond
   [(not binding)
    (error "unbound identifier:" s)]
   [else
    ;; Variable or form as identifier macro
    (dispatch (lookup binding env s) s env phase)]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s env phase)
  (define id (car (syntax-e s)))
  (define binding (resolve id phase))
  (define t (if binding
                (lookup binding env id)
                missing))
  ;; Find out whether it's bound as a variable, syntax, or core form
  (cond
   [(or (variable? t) (missing? t))
    (expand-app s env phase)]
   [else
    ;; Syntax or core form as "application"
    (dispatch t s env phase)]))

;; Expand `s` given that the value `t` of the relevant binding,
;; where `t` is either a core form, a macro transformer, some
;; other compile-time value (which is an error), or a token
;; indicating that the binding is a run-time variable
(define (dispatch t s env phase)
  (cond
   [(core-form? t)
    ((core-form-expander t) s env phase)]
   [(transformer? t)
    ;; Apply transformer and expand again
    (expand (apply-transformer t s) env phase)]
   [(variable? t)
    ;; A reference to a variable expands to itself
    s]
   [else
    ;; Some other compile-time value:
    (error "illegal use of syntax:" t)]))

;; Given a macro transformer `t`, apply it --- adding appropriate
;; mark to represent the expansion step
(define (apply-transformer t s)
  (define m (gensym 't))
  (define marked-s (mark s m))
  ;; Call the transformer
  (define transformed-s (t marked-s))
  (unless (syntax? transformed-s)
    (error "transformer produced non-syntax:" transformed-s))
  ;; Flip mark to get final result:
  (mark transformed-s m))

;; Helper to lookup a binding with core forms
(define (lookup b env id)
  (binding-lookup b core-forms env id))

;; ----------------------------------------

;; Expand an application (i.e., a function call)
(define (expand-app s env phase)
  (define m (match-syntax s '(rator rand ...)))
  (rebuild
   s
   (list* (core-literal '#%app phase)
          (expand (m 'rator) env phase)
          (for/list ([e (in-list (m 'rand))])
            (expand e env phase)))))

;; ----------------------------------------

;; Expand `s` as a compile-time expression
(define (expand-transformer s env phase)
  (expand (introduce s (core-branch phase))
          empty-env phase))

;; Expand and evaluate `s` as a compile-time expression
(define (eval-for-syntax-binding rhs env phase)
  (define exp-rhs (expand-transformer rhs env (add1 phase)))
  (expand-time-eval (compile exp-rhs (add1 phase))))

;; ----------------------------------------

;; A helper for forms to reconstruct syntax
(define (rebuild orig-s new)
  (datum->syntax orig-s new))
