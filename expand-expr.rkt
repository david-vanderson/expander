#lang racket/base
(require racket/set
         "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "binding.rkt"
         "core.rkt"
         "expand.rkt")

;; ----------------------------------------

(add-core-form!
 'lambda
 (lambda (s env phase)
   (define m (match-syntax s '(lambda (id ...) body)))
   (define branchid (gensym 'lambda))
   (define newbranches (make-newbranches))
   (define ids (extend-branch (m 'id) branchid newbranches))
   (define body (extend-branch (m 'body) branchid newbranches))
   ;; Bind each argument and generate a corresponding key for the
   ;; expand-time environment:
   (define keys (for/list ([id (in-list ids)])
                  (define key (gensym (syntax-e id)))
                  (define b (local-binding key))
                  (add-binding! id (syntax-e id) phase b newbranches)
                  key))
   (define body-env (for/fold ([env env]) ([key (in-list keys)])
                      (env-extend env key variable)))
   ;; Expand the function body:
   (define exp-body (expand body body-env phase))
   (rebuild
    s
    `(,(m 'lambda) ,ids ,exp-body))))

;; ----------------------------------------

(add-core-form!
 'let-syntax
 (lambda (s env phase)
   (define m (match-syntax s '(let-syntax ([trans-id trans-rhs]
                                           ...)
                                 body)))

   (define branchid (gensym 'let-syntax))
   (define newbranches (make-newbranches))
   (define trans-ids (extend-branch (m 'trans-id) branchid newbranches))
   (define body (extend-branch (m 'body) branchid newbranches))

   ;; Evaluate compile-time expressions before binding:
   (define trans-vals (for/list ([rhs (in-list (m 'trans-rhs))])
                        (eval-for-syntax-binding rhs env phase)))
   
   ;; Bind each left-hand identifier and generate a corresponding key
   ;; for the expand-time environment:
   (define trans-keys (for/list ([id (in-list trans-ids)])
                        (define key (gensym (syntax-e id)))
                        (define b (local-binding key))
                        (add-binding! id (syntax-e id) phase b newbranches)
                        key))
   
   ;; Fill expansion-time environment:
   (define body-env (for/fold ([env env]) ([key (in-list trans-keys)]
                                           [val (in-list trans-vals)])
                      (env-extend env key val)))
   ;; Expand body
   (expand body body-env phase)))

;; ----------------------------------------

(add-core-form!
 '#%app
 (lambda (s env phase)
   (define m (match-syntax s '(#%app rator rand ...)))
   (rebuild
    s
    (list* (m '#%app)
           (expand (m 'rator) env)
           (for/list ([rand (in-list (m 'rand))])
             (expand rand env))))))

(add-core-form!
 'quote
 (lambda (s env phase)
   (match-syntax s '(quote datum))
   s))

(add-core-form!
 'quote-syntax
 (lambda (s env phase)
   (match-syntax s '(quote-syntax datum))
   s))
