#lang racket
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "expand.rkt"
         "expand-context.rkt"
         "compile.rkt")

(provide coreb)


(define (coreb phase)

  (define cb (branch 'core null))
  
  (define-syntax (append-core! stx)
    (syntax-case stx ()
      ((_ bind)
       #'(set-branch-binds! cb (cons bind (branch-binds cb))))))

  ;; Register core primitives
  ;; Enough primitives for examples...
  (append-core! (bind phase 'syntax-e 'prim syntax-e))
  (append-core! (bind phase 'datum->syntax 'prim datum->syntax))
  (append-core! (bind phase 'cons 'prim cons))
  (append-core! (bind phase 'list 'prim list))
  (append-core! (bind phase 'car 'prim car))
  (append-core! (bind phase 'cdr 'prim cdr))
  (append-core! (bind phase 'null? 'prim null?))
  (append-core! (bind phase 'map 'prim map))
  (append-core! (bind phase 'values 'prim values))
  (append-core! (bind phase 'bound-identifier=? 'prim bound-identifier=?))


  ;; define-values and define-syntaxes are only recognized inside
  ;; a definition context, and are handled there
  (append-core! (bind phase 'define-values 'form
                      (lambda (s ctx)
                        (error "define-values not allowed in an expression position:" s))))

  (append-core! (bind phase 'define-syntaxes 'form
                      (lambda (s ctx)
                        (error "define-syntaxes not allowed in an expression position:" s))))


  (define (check-no-duplicate-ids id-list phase)
    (cond
      [(or (null? id-list)
           (null? (cdr id-list)))
       #t]
      [else
       (define id (car id-list))
       (for ((other-id (in-list (cdr id-list))))
         (when (bound-identifier=? id other-id phase)
           (error "duplicate binding:" other-id)))
       (check-no-duplicate-ids (cdr id-list) phase)]))


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


  ;; Common expansion for `lambda` and `case-lambda`
  (define (make-lambda-expander s formals bodys ctx)
    ;(printf "lambda-expander expanding ~v\n~v\n\n" (syntax->datum formals) (map syntax->datum bodys))
    ;; Parse and check formal arguments:
    (define ids (parse-and-flatten-formals formals))
    (check-no-duplicate-ids ids (expand-context-phase ctx))
  
    (define branchid (gensym 'lambda))
    (define newbranches (make-newbranches))
    (set! ids (extend-branch ids branchid newbranches))
    (set! bodys (extend-branch bodys branchid newbranches))
    (for ([id (in-list ids)])
      (define sym (syntax-e id))
      (define b (bind (expand-context-phase ctx) sym 'var (gensym sym)))
      ;; Add the new binding
      (add-binding! id b newbranches))

    ;; Expand the function body:
    ;(define exp-body (expand (car bodys) ctx))
    (define exp-body (expand-body s bodys ctx))
  
    (values ids exp-body))


  (append-core! (bind phase 'lambda 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(lambda formals body ...+)))
                        (define-values (formals body)
                          (make-lambda-expander s (m 'formals) (m 'body) ctx))
   
                        (rebuild s (list (m 'lambda) formals body)))))


  (append-core! (bind phase 'case-lambda 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(case-lambda [formals body ...+] ...)))
                        (define cm (match-syntax s '(case-lambda clause ...)))
                        (rebuild s
                                 `(,(m 'case-lambda)
                                   ,@(for/list ([formals (in-list (m 'formals))]
                                                [bodys (in-list (m 'body))]
                                                [clause (in-list (cm 'clause))])
                                       (define-values (exp-formals exp-body)
                                         (make-lambda-expander s formals bodys ctx))
                                       (rebuild clause `[,exp-formals ,exp-body])))))))


  ;; Common expansion for `let[rec]-[syntaxes+]values`
  (define (make-let-values-form letsym syntaxes? rec?)
    (lambda (s ctx)
      (define m (if syntaxes?
                    (match-syntax s '(let-syntax-id
                                      ([(trans-id ...) trans-rhs] ...)
                                      ([(val-id ...) val-rhs] ...)
                                      body ...+))
                    (match-syntax s '(let-id ([(val-id ...) val-rhs] ...)
                                             body ...+))))
    
      (define transids (if syntaxes? (m 'trans-id) null))
      (define transs (if syntaxes? (m 'trans-rhs) null))
      (define valids (m 'val-id))
      (define valrhs (m 'val-rhs))
      (define bodys (m 'body))

      ;(printf "make-let-values body is ~v\n\n" (map syntax->datum bodys))

      (when (not rec?)
        ;; expand+eval trans-rhs before binding
        (set! transs
              (for/list ([ids (in-list transids)]
                         [rhs (in-list transs)])
                (eval-for-syntaxes-binding rhs ids ctx)))

        ; expand val-rhs before binding
        (set! valrhs
              (for/list ([rhs (in-list valrhs)])
                (expand rhs ctx))))

      ;; do the binding part
      (define branchid (gensym letsym))
      (define newbranches (make-newbranches))
      (set! transids (extend-branch transids branchid newbranches))
      (when rec? (set! transs (extend-branch transs branchid newbranches)))
      (set! valids (extend-branch valids branchid newbranches))
      (when rec? (set! valrhs (extend-branch valrhs branchid newbranches)))
      (set! bodys (extend-branch bodys branchid newbranches))
    
      (for ([ids (in-list transids)]
            [trans (in-list (if rec? transids transs))])
        (for ([id (in-list ids)]
              [t (in-list trans)])
          (define sym (syntax-e id))
          (define b (bind (expand-context-phase ctx) sym 'stx (if rec? #f t)))
          ;; Add the new binding
          (add-binding! id b newbranches)))

      (for ([ids (in-list valids)])
        (for ([id (in-list ids)])
          (define sym (syntax-e id))
          (define b (bind (expand-context-phase ctx) sym 'var (gensym sym)))
          ;; Add the new binding
          (add-binding! id b newbranches)))

      (when rec?
        ;; expand+eval trans-rhs after binding
        ;; go back through each trans-id, find the binding,
        ;; and replace its dummy val with the transformer
        (for ([ids (in-list transids)]
              [rhs (in-list transs)])
          (define transformers
            (eval-for-syntaxes-binding rhs ids ctx))
        
          (for ([id (in-list ids)]
                [trans (in-list transformers)])
            (define binding (resolve id (expand-context-phase ctx) #t))
            (set-bind-val! binding trans)))

        ; expand val-rhs in presence of bindings
        (set! valrhs
              (for/list ([rhs (in-list valrhs)])
                (expand rhs ctx))))

      ;; expand body
      ;(define exp-body (expand (car bodys) ctx))
      (define exp-body (expand-body s bodys ctx))

      ;; create the new syntax using let[rec]-values
      (rebuild s
               `(,(literal (if rec? 'letrec-values 'let-values) ctx)
                 ,(for/list ([ids (in-list valids)]
                             [rhs (in-list valrhs)])
                    `[,ids ,rhs])
                 ,exp-body))))

  (append-core! (bind phase 'let-values 'form
                      (make-let-values-form 'let-values #f #f)))

  (append-core! (bind phase 'letrec-values 'form
                      (make-let-values-form 'letrec-values #f #t)))

  (append-core! (bind phase 'letrec-syntaxes+values 'form
                      (make-let-values-form 'letrec-syntaxes+values #t #t)))


  (append-core! (bind phase 'let-syntax 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(let-syntax ([trans-id trans-rhs]
                                                                ...)
                                                     body)))
                        (define body (m 'body))
                        (define tids (m 'trans-id))
                        ;; Evaluate compile-time expressions:
                        (define trans-vals (for/list ([rhs (in-list (m 'trans-rhs))])
                                             ; car because this returns a list of the values produced,
                                             ; and let-syntax only supports a single value
                                             (car (eval-for-syntaxes-binding rhs tids ctx))))
  
                        (define branchid (gensym 'let-syntax))
                        (define newbranches (make-newbranches))
                        (set! tids (extend-branch tids branchid newbranches))
                        (set! body (extend-branch body branchid newbranches))
                        (for ([id (in-list tids)]
                              [t (in-list trans-vals)])
                          (define sym (syntax-e id))
                          (define b (bind (expand-context-phase ctx) sym 'stx t))
                          ;; Add the new binding
                          (add-binding! id b newbranches))
    
                        ;; Expand body
                        (define exp-body (expand body ctx))

                        exp-body)))


  (append-core! (bind phase '#%datum 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(#%datum . datum)))
                        (when (keyword? (syntax-e (m 'datum)))
                          (error "keyword misused as an expression:" (m 'datum)))
                        ;; core form of #%datum expands to literal 'quote
                        (rebuild s (list (literal 'quote ctx)
                                         (m 'datum))))))

  (append-core! (bind phase '#%app 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(#%app rator rand ...)))
                        (rebuild s
                                 (list* (m '#%app)
                                        (expand (m 'rator) ctx)
                                        (for/list ([rand (in-list (m 'rand))])
                                          (expand rand ctx)))))))

  (append-core! (bind phase '#%top 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(#%top-id . datum)))
                        (error "unbound identifier in:" (m 'datum)))))


  (append-core! (bind phase 'quote 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(quote datum)))
                        ;; core form of 'quote expands to literal 'quote
                        (rebuild s (list (m 'quote) (m 'datum))))))


  (append-core! (bind phase 'quote-syntax 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(quote-syntax datum)))
                        ;; core form of 'quote-syntax expands to literal 'quote-syntax
                        (rebuild s (list (m 'quote-syntax)
                                         (m 'datum))))))


  (append-core! (bind phase 'if 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(if tst thn els)))
                        (rebuild s
                                 (list (m 'if)
                                       (expand (m 'tst) ctx)
                                       (expand (m 'thn) ctx)
                                       (expand (m 'els) ctx))))))

  (append-core! (bind phase 'with-continuation-mark 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(with-continuation-mark key val body)))
                        (rebuild s
                                 (list (m 'with-continuation-mark)
                                       (expand (m 'key) ctx)
                                       (expand (m 'val) ctx)
                                       (expand (m 'body) ctx))))))


  (define (make-begin)
    (lambda (s ctx)
      (define m (match-syntax s '(begin-id e ...+)))
      (rebuild s
               (cons (m 'begin-id)
                     (for/list ([e (in-list (m 'e))])
                       (expand e ctx))))))

  (append-core! (bind phase 'begin 'form (make-begin)))
  (append-core! (bind phase 'begin0 'form (make-begin)))

  (append-core! (bind phase 'set! 'form
                      (lambda (s ctx)
                        (define m (match-syntax s '(set! id rhs)))
                        (define binding (resolve (m 'id) (expand-context-phase ctx)))
                        (unless binding
                          (error "no binding for assignment:" s))
                        (when (or (equal? 'stx (bind-type binding))
                                  (equal? 'form (bind-type binding)))
                          (error "cannot assign to syntax:" s))
                        (when (equal? 'prim (bind-type binding))
                          (error "cannot assign to primitive:" s))
                        (rebuild s
                                 (list (literal 'set! ctx)
                                       (m 'id)
                                       (expand (m 'rhs) ctx))))))

  cb)
  