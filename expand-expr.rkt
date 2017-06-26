#lang racket/base
(require racket/set
         "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "namespace.rkt"
         "binding.rkt"
         "dup-check.rkt"
         "core.rkt"
         "expand-context.rkt"
         "expand.rkt")

;; ----------------------------------------

;; Common expansion for `lambda` and `case-lambda`
(define (make-lambda-expander s formals bodys ctx)
  (define phase (expand-context-phase ctx))
  ;; Parse and check formal arguments:
  (define ids (parse-and-flatten-formals formals))
  (check-no-duplicate-ids ids phase s)

  ;; Create the branch for this binding context
  (define branchid (gensym 'lambda))
  (define newbranches (make-newbranches))
  (set! ids (extend-branch ids branchid newbranches))
  (set! bodys (extend-branch bodys branchid newbranches))

  (define body-env
    (for/fold ([env (expand-context-env ctx)])
              ([id (in-list ids)])
      (define key (gensym (syntax-e id)))
      ;; make a binding and add it to all syntax
      (define b (local-binding key))
      (add-binding! id (syntax-e id) phase b newbranches)
      ;; extend the environment
      (env-extend env key variable)))
  
  ;; Expand the function body:
  (define body-ctx (struct-copy expand-context ctx
                                [env body-env]))
  (define exp-body (expand-body bodys s body-ctx))
  
  ;; Return formals (with new bindings) and expanded body:
  (values ids exp-body))

(add-core-form!
 'lambda
 (lambda (s ctx)
   (define m (match-syntax s '(lambda formals body ...+)))
   (define-values (formals body)
     (make-lambda-expander s (m 'formals) (m 'body) ctx))
   (rebuild
    s
    `(,(m 'lambda) ,formals ,body))))

(add-core-form!
 'case-lambda
 (lambda (s ctx)
   (define m (match-syntax s '(case-lambda [formals body ...+] ...)))
   (define cm (match-syntax s '(case-lambda clause ...)))
   (rebuild
    s
    `(,(m 'case-lambda)
      ,@(for/list ([formals (in-list (m 'formals))]
                   [bodys (in-list (m 'body))]
                   [clause (in-list (cm 'clause))])
          (define-values (exp-formals exp-body)
            (make-lambda-expander s formals bodys ctx))
          (rebuild clause `[,exp-formals ,exp-body]))))))

(define (parse-and-flatten-formals all-formals)
  (let loop ([formals all-formals])
    (cond
     [(identifier? formals) (list formals)]
     [(syntax? formals)
      (define p (syntax-e formals))
      (cond
       [(pair? p) (loop p)]
       [(null? p) null]
       [else (error "not an identifier:" p)])]
     [(pair? formals)
      (unless (identifier? (car formals))
        (error "not an identifier:" (car formals)))
      (cons (car formals)
            (loop (cdr formals)))]
     [(null? formals)
      null]
     [else
      (error "bad argument sequence:" all-formals)])))

;; ----------------------------------------

;; Common expansion for `let[rec]-[syntaxes+]values`
(define (make-let-values-form letsym syntaxes? rec?)
  (lambda (s ctx)
    (define m (if syntaxes?
                  (match-syntax s '(letrec-syntaxes+values
                                    ([(trans-id ...) trans-rhs] ...)
                                    ([(val-id ...) val-rhs] ...)
                                    body ...+))
                  (match-syntax s '(let-values ([(val-id ...) val-rhs] ...)
                                    body ...+))))

    (define phase (expand-context-phase ctx))
    (define transids (if syntaxes? (m 'trans-id) null))
    (define transs (if syntaxes? (m 'trans-rhs) null))
    (define valids (m 'val-id))
    (define valrhs (m 'val-rhs))
    (define bodys (m 'body))

    (check-no-duplicate-ids (list transids valids) phase s)

    (when (not rec?)
      ;; expand+eval transformer rhs before binding
      (set! transs
            (for/list ([ids (in-list transids)]
                       [rhs (in-list transs)])
              (eval-for-syntaxes-binding rhs ids ctx)))
      
      ; expand value rhs before binding
      (set! valrhs
            (for/list ([rhs (in-list valrhs)])
              (expand rhs ctx))))

    ;; Create the binding branch for this context
    (define branchid (gensym letsym))
    (define newbranches (make-newbranches))
    (set! transids (extend-branch transids branchid newbranches))
    (when rec? (set! transs (extend-branch transs branchid newbranches)))
    (set! valids (extend-branch valids branchid newbranches))
    (when rec? (set! valrhs (extend-branch valrhs branchid newbranches)))
    (set! bodys (extend-branch bodys branchid newbranches))

    ;; Bind each trans id
    (define trans-keyss
      (for/list ([ids (in-list transids)])
        (for/list ([id (in-list ids)])
          (define key (gensym (syntax-e id)))
          ;; make a binding and add it to all syntax
          (define b (local-binding key))
          (add-binding! id (syntax-e id) phase b newbranches)
          key)))

    ;; Bind each val id
    (define val-keyss
      (for/list ([ids (in-list valids)])
        (for/list ([id (in-list ids)])
          (define key (gensym (syntax-e id)))
          ;; make a binding and add it to all syntax
          (define b (local-binding key))
          (add-binding! id (syntax-e id) phase b newbranches)
          key)))

    (when rec?
      ;; expand+eval transformer rhs after binding
      (set! transs
            (for/list ([ids (in-list transids)]
                       [rhs (in-list transs)])
              (eval-for-syntaxes-binding rhs ids ctx))))

    ;; Extend environment
    (define rec-val-env
      (for*/fold ([env (expand-context-env ctx)]) ([keys (in-list val-keyss)]
                                                   [key (in-list keys)])
        (env-extend env key variable)))
    (define rec-env (for/fold ([env rec-val-env]) ([keys (in-list trans-keyss)]
                                                   [vals (in-list transs)])
                      (for/fold ([env env]) ([key (in-list keys)]
                                             [val (in-list vals)])
                        (env-extend env key val))))

    (define rec-ctx (struct-copy expand-context ctx
                                 [env rec-env]))

    (when rec?
      ; expand value rhs in presence of bindings and extended environment
      (set! valrhs
            (for/list ([rhs (in-list valrhs)])
              (expand rhs rec-ctx))))

    ; Expand body
    (define exp-body (expand-body bodys s rec-ctx))

    ; create new syntax using let[rec]-values
    (rebuild
     s
     `(,(core-literal (if rec? 'letrec-values 'let-values) phase)
       ,(for/list ([ids (in-list valids)]
                   [rhs (in-list valrhs)])
          `[,ids ,rhs])
       ,exp-body))))

(add-core-form!
 'let-values
 (make-let-values-form 'let-values #f #f))

(add-core-form!
 'letrec-values
 (make-let-values-form 'letrec-values #f #t))

(add-core-form!
 'letrec-syntaxes+values
 (make-let-values-form 'letrec-syntaxes+values #t #t))

;; ----------------------------------------

(add-core-form!
 '#%datum
 (lambda (s ctx)
   (define m (match-syntax s '(#%datum . datum)))
   (when (keyword? (syntax-e (m 'datum)))
     (error "keyword misused as an expression:" (m 'datum)))
   (rebuild
    s
    (list (core-literal 'quote (expand-context-phase ctx))
          (m 'datum)))))

(add-core-form!
 '#%app
 (lambda (s ctx)
   (define m (match-syntax s '(#%app rator rand ...)))
   (rebuild
    s
    (list* (m '#%app)
           (expand (m 'rator) ctx)
           (for/list ([rand (in-list (m 'rand))])
             (expand rand ctx))))))

(add-core-form!
 'quote
 (lambda (s ctx)
   (match-syntax s '(quote datum))
   s))

(add-core-form!
 'quote-syntax
 (lambda (s ctx)
   (define m (match-syntax s '(quote-syntax datum)))
   (rebuild
    s
    `(,(m 'quote-syntax)
      ,(m 'datum)))))

(add-core-form!
 'if
 (lambda (s ctx)
   (define m (match-syntax s '(if tst thn els)))
   (rebuild
    s
    (list (m 'if)
          (expand (m 'tst) ctx)
          (expand (m 'thn) ctx)
          (expand (m 'els) ctx)))))

(add-core-form!
 'with-continuation-mark
 (lambda (s ctx)
   (define m (match-syntax s '(with-continuation-mark key val body)))
   (rebuild
    s
    (list (m 'with-continuation-mark)
          (expand (m 'key) ctx)
          (expand (m 'val) ctx)
          (expand (m 'body) ctx)))))

(define (make-begin)
 (lambda (s ctx)
   (define m (match-syntax s '(begin e ...+)))
   (rebuild
    s
    (cons (m 'begin)
          (for/list ([e (in-list (m 'e))])
            (expand e ctx))))))

(add-core-form!
 'begin
 (make-begin))

(add-core-form!
 'begin0
 (make-begin))

(add-core-form!
 'set!
 (lambda (s ctx)
   (define m (match-syntax s '(set! id rhs)))
   (define binding (resolve (m 'id) (expand-context-phase ctx)))
   (unless binding
     (error "no binding for assignment:" s))
   (define t (lookup binding ctx s))
   (unless (variable? t)
     (error "cannot assign to syntax:" s))
   (rebuild
    s
    (list (m 'set!)
          (m 'id)
          (expand (m 'rhs) ctx)))))
