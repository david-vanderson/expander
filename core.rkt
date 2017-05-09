#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "expand.rkt"
         "compile.rkt")

(provide namespace-syntax-introduce)


;; Expand and evaluate `s` as a compile-time expression
(define (eval-for-syntax-binding rhs phase)
  ;(printf "eval-for-syntax\n\n")
  (define nsi (namespace-syntax-introduce rhs phase))
  ;(printf "eval-for-syntax2\n\n")
  (define exp-rhs (expand nsi phase))
  ;(printf "eval-for-syntax3\n\n")
  (define exp-comp (compile exp-rhs phase))
  ;(printf "eval-for-syntax4\n\n")
  (expand-time-eval exp-comp))


(define coret (tip 'coret #f #f))


(define (namespace-syntax-introduce s
                                    (phase 0)
                                    (t (tip (gensym 'tipcore) phase (tip-branch coret))))
  (cond
    [(syntax? s)
     (syntax (namespace-syntax-introduce (syntax-e s) phase t) (syntax-mark s)
             (if (syntax-tip s phase)
                 (error "already have a tip for this phase" phase s)
                 (cons t (syntax-tips s))))]
    [(list? s) (map (lambda (v) (namespace-syntax-introduce v phase t)) s)]
    [else s]))


;; Register core primitives
;; Enough primitives for examples...
(tip-extend! coret 'syntax-e 'prim syntax-e)
(tip-extend! coret 'datum->syntax 'prim datum->syntax)
(tip-extend! coret 'cons 'prim cons)
(tip-extend! coret 'list 'prim list)
(tip-extend! coret 'car 'prim car)
(tip-extend! coret 'cdr 'prim cdr)
(tip-extend! coret 'null? 'prim null?)
(tip-extend! coret 'map 'prim map)


;; Register core forms
(tip-extend! coret 'lambda 'form
  (lambda (s phase)
    (define m (match-syntax s '(lambda-id (id ...) body)))
    (define old-tips (list))
    (define ids
      (for/list ([id (in-list (m 'id))])
        ;; Get the tip from the binding variable
        (define t (syntax-tip id phase #t))
        (define sym (syntax-e id))
        ;; Add the new binding
        (tip-extend! t sym 'var (gensym sym))
        ;; save this old tip before we freeze so we can pop it later
        (set! old-tips (cons t old-tips))
        ;; Freeze binding branch on id
        (freeze id)))
    ;; Expand the function body:
    (define exp-body (expand (m 'body) phase))
    ;; Remove the new bindings
    (for ([t (in-list old-tips)])
      (tip-pop! t))

    ;; the lambda core form always results in a literal 'lambda
    (define litlambda (freeze (namespace-syntax-introduce (datum->syntax #f 'lambda) phase)))

    (freeze (datum->syntax s (list litlambda ids exp-body)))))


(tip-extend! coret 'let-syntax 'form
  (lambda (s phase)
    (define m (match-syntax s '(let-syntax ([trans-id trans-rhs]
                                           ...)
                                 body)))
    (define old-tips (list))
    ;; Evaluate compile-time expressions:
    (define trans-vals (for/list ([rhs (in-list (m 'trans-rhs))])
                         (eval-for-syntax-binding rhs (+ phase 1))))

    ;; Bind each left-hand identifier
    (define trans-keys
      (for/list ([id (in-list (m 'trans-id))]
                 [trans (in-list trans-vals)])
        (define t (syntax-tip id phase #t))
        (define sym (syntax-e id))
        ;; Add the new binding
        (tip-extend! t sym 'stx trans)
        ;; save this old tip before we freeze so we can pop it later
        (set! old-tips (cons t old-tips))
        ;; Freeze binding branch on id
        (freeze id)))

    ;(printf "expanding body\n")
    ;; Expand body
    (define exp-body (expand (m 'body) phase))
    ;; Remove the new bindings
    (for ([t (in-list old-tips)])
      (tip-pop! t))

    exp-body))


(tip-extend! coret '#%app 'form
  (lambda (s phase)
    (define m (match-syntax s '(#%app-id rator rand ...)))
    ;; core form of #%app leaves a literal '#%app
    (define litapp (freeze (namespace-syntax-introduce (datum->syntax #f '#%app) phase)))
    (freeze (datum->syntax s
                           (list* litapp
                                  (expand (m 'rator) phase)
                                  (for/list ([rand (in-list (m 'rand))])
                                    (expand rand phase)))))))


(tip-extend! coret 'quote 'form
  (lambda (s phase)
    (define m (match-syntax s '(quote datum)))
    (define litquote (freeze (namespace-syntax-introduce (datum->syntax #f 'quote) phase)))
    (freeze (datum->syntax s (list litquote (m 'datum))))))


(tip-extend! coret 'quote-syntax 'form
  (lambda (s phase)
    (define m (match-syntax s '(quote-syntax datum)))
    (define litquote-syntax (freeze (namespace-syntax-introduce
                                     (datum->syntax #f 'quote-syntax) phase)))
    (freeze (datum->syntax s (list litquote-syntax (m 'datum))))))

