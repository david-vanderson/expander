#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "expand.rkt"
         "expand-context.rkt"
         "compile.rkt")

(provide coret)


(define coret (tip 'coret #f #f))


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
(tip-extend! coret 'values 'prim values)
(tip-extend! coret 'bound-identifier=? 'prim bound-identifier=?)


;; define-values and define-syntaxes are only recognized inside
;; a definition context, and are handled there
(tip-extend! coret 'define-values 'form
  (lambda (s ctx)
    (error "define-values not allowed in an expression position:" s)))

(tip-extend! coret 'define-syntaxes 'form
  (lambda (s ctx)
    (error "define-syntaxes not allowed in an expression position:" s)))


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
  ;; Parse and check formal arguments:
  (define ids (parse-and-flatten-formals formals))
  (check-no-duplicate-ids ids (expand-context-phase ctx))
  (define old-tips (list))
  (define exp-ids
    (for/list ([id (in-list ids)])
      ;; Get the tip from the binding variable
      (define t (syntax-tip id (expand-context-phase ctx) #t))
      (define sym (syntax-e id))
      ;; Add the new binding
      (tip-extend! t sym 'var (gensym sym))
      ;; save this old tip before we freeze so we can pop it later
      (set! old-tips (cons t old-tips))
      ;; Freeze binding branch on id
      (freeze id)))
  ;; Expand the function body:
  ;(define exp-body (expand (car bodys) ctx))
  (define exp-body (expand-body s bodys ctx))
  ;; Remove the new bindings
  (for ([t (in-list old-tips)])
    (tip-pop! t))

  (values exp-ids exp-body))


(tip-extend! coret 'lambda 'form
 (lambda (s ctx)
   (define m (match-syntax s '(lambda-id formals body ...+)))
   (define-values (formals body)
     (make-lambda-expander s (m 'formals) (m 'body) ctx))
   
   ;; the core form always results in a literal 'lambda
   (freeze (rebuild s (list (literal 'lambda ctx) formals body)))))


(tip-extend! coret 'case-lambda 'form
 (lambda (s ctx)
   (define m (match-syntax s '(case-lambda [formals body ...+] ...)))
   (define cm (match-syntax s '(case-lambda clause ...)))

   ;; the core form always results in a literal 'case-lambda
   (freeze (rebuild s
             `(,(literal 'case-lambda ctx)
               ,@(for/list ([formals (in-list (m 'formals))]
                            [bodys (in-list (m 'body))]
                            [clause (in-list (cm 'clause))])
                   (define-values (exp-formals exp-body)
                     (make-lambda-expander s formals bodys ctx))
                   (rebuild clause `[,exp-formals ,exp-body])))))))


;; Common expansion for `let[rec]-[syntaxes+]values`
(define (make-let-values-form syntaxes? rec?)
  (lambda (s ctx)
    (define m (if syntaxes?
                  (match-syntax s '(let-syntax-id
                                    ([(trans-id ...) trans-rhs] ...)
                                    ([(val-id ...) val-rhs] ...)
                                    body ...+))
                  (match-syntax s '(let-id ([(val-id ...) val-rhs] ...)
                                    body ...+))))
    
    (define old-tips null)
    (define maybe-transids #f)  ; possible list of bound trans-ids
    (define maybe-transs #f)  ; possible list of transformers
    (define exp-rhs #f)

    (when (not rec?)
      ;; expand+eval trans-rhs before binding
      (when syntaxes?
        (set! maybe-transs
              (for/list ([ids (in-list (m 'trans-id))]
                         [rhs (in-list (m 'trans-rhs))])
                (eval-for-syntaxes-binding rhs ids ctx))))

      ; expand val-rhs before binding
      (set! exp-rhs
            (for/list ([rhs (in-list (m 'val-rhs))])
              (expand rhs ctx))))

    ;; do the binding part
    (when syntaxes?
      (set! maybe-transids
            (for/list ([ids (in-list (m 'trans-id))]
                       [transs (in-list (if rec?
                                            (m 'trans-id)  ; unused, but the right length
                                            maybe-transs))])
              (for/list ([id (in-list ids)]
                         [trans (in-list transs)])
                ;; Get the tip from the binding variable
                (define t (syntax-tip id (expand-context-phase ctx) #t))
                (define sym (syntax-e id))
                ;; Add the new binding
                (tip-extend! t sym 'stx (if rec? #f trans))
                ;; save this old tip before we freeze so we can pop it later
                (set! old-tips (cons t old-tips))
                ;; Freeze binding branch on id
                (freeze id)))))

    (define exp-val-ids
      (for/list ([ids (in-list (m 'val-id))])
        (for/list ([id (in-list ids)])
          ;; Get the tip from the binding variable
          (define t (syntax-tip id (expand-context-phase ctx) #t))
          (define sym (syntax-e id))
          ;; Add the new binding
          (tip-extend! t sym 'var (gensym sym))
          ;; save this old tip before we freeze so we can pop it later
          (set! old-tips (cons t old-tips))
          ;; Freeze binding branch on id
          (freeze id))))

    (when rec?
      ;; expand+eval trans-rhs after binding
      (when syntaxes?
        ;; go back through each trans-id, find the binding,
        ;; and replace its dummy val with the transformer
        (for ([ids (in-list maybe-transids)]
              [rhs (in-list (m 'trans-rhs))])
          (define transformers
            (eval-for-syntaxes-binding rhs ids ctx))
          
          (for ([id (in-list ids)]
                [trans (in-list transformers)])
            (define binding (resolve id (expand-context-phase ctx) #t))
            (set-bind-val! binding trans))))

      ; expand val-rhs in presence of bindings
      (set! exp-rhs
            (for/list ([rhs (in-list (m 'val-rhs))])
              (expand rhs ctx))))

    ;; expand body
    ;(define exp-body (expand (car (m 'body)) ctx))
    (define exp-body (expand-body s (m 'body) ctx))
    
    ;; Remove the new bindings
    (for ([t (in-list old-tips)])
      (tip-pop! t))

    ;; create the new syntax using let[rec]-values
    (freeze (rebuild s
             `(,(literal (if rec? 'letrec-values 'let-values) ctx)
               ,(for/list ([ids (in-list exp-val-ids)]
                           [rhs (in-list exp-rhs)])
                  `[,ids ,rhs])
               ,exp-body)))))

(tip-extend! coret 'let-values 'form
 (make-let-values-form #f #f))

(tip-extend! coret 'letrec-values 'form
 (make-let-values-form #f #t))

(tip-extend! coret 'letrec-syntaxes+values 'form
 (make-let-values-form #t #t))


(tip-extend! coret 'let-syntax 'form
  (lambda (s ctx)
    (define m (match-syntax s '(let-syntax ([trans-id trans-rhs]
                                           ...)
                                 body)))
    (define old-tips (list))
    ;; Evaluate compile-time expressions:
    (define trans-vals (for/list ([rhs (in-list (m 'trans-rhs))])
                         ; car because this returns a list of the values produced,
                         ; and let-syntax only supports a single value
                         (car (eval-for-syntaxes-binding rhs (m 'trans-id) ctx))))

    ;; Bind each left-hand identifier
    (define trans-keys
      (for/list ([id (in-list (m 'trans-id))]
                 [trans (in-list trans-vals)])
        (define t (syntax-tip id (expand-context-phase ctx) #t))
        (define sym (syntax-e id))
        ;; Add the new binding
        (tip-extend! t sym 'stx trans)
        ;; save this old tip before we freeze so we can pop it later
        (set! old-tips (cons t old-tips))
        ;; Freeze binding branch on id
        (freeze id)))

    ;(printf "expanding body\n")
    ;; Expand body
    (define exp-body (expand (m 'body) ctx))
    ;; Remove the new bindings
    (for ([t (in-list old-tips)])
      (tip-pop! t))

    exp-body))


(tip-extend! coret '#%datum 'form
 (lambda (s ctx)
   (define m (match-syntax s '(#%datum . datum)))
   (when (keyword? (syntax-e (m 'datum)))
     (error "keyword misused as an expression:" (m 'datum)))
   ;; core form of #%datum expands to literal 'quote
   (freeze (rebuild s (list (literal 'quote ctx)
                            (m 'datum))))))

(tip-extend! coret '#%app 'form
  (lambda (s ctx)
    (define m (match-syntax s '(#%app-id rator rand ...)))
    ;; core form of #%app leaves a literal '#%app
    (freeze (rebuild s
                     (list* (literal '#%app ctx)
                            (expand (m 'rator) ctx)
                            (for/list ([rand (in-list (m 'rand))])
                              (expand rand ctx)))))))

(tip-extend! coret '#%top 'form
  (lambda (s ctx)
    (define m (match-syntax s '(#%top-id . datum)))
    (error "unbound identifier in:" (m 'datum))))


(tip-extend! coret 'quote 'form
  (lambda (s ctx)
    (define m (match-syntax s '(quote datum)))
    ;; core form of 'quote expands to literal 'quote
    (freeze (rebuild s (list (literal 'quote ctx) (m 'datum))))))


(tip-extend! coret 'quote-syntax 'form
  (lambda (s ctx)
    (define m (match-syntax s '(quote-syntax datum)))
    ;; core form of 'quote-syntax expands to literal 'quote-syntax
    (freeze (rebuild s (list (literal 'quote-syntax ctx)
                             (m 'datum)))
            ; this is the only freeze where we pass the ctx so
            ; that if we are in a definition context in some phase
            ; those tips won't be fully frozen
            ctx)))


(tip-extend! coret 'if 'form
 (lambda (s ctx)
   (define m (match-syntax s '(if tst thn els)))
   (freeze (rebuild s
                    (list (m 'if)
                          (expand (m 'tst) ctx)
                          (expand (m 'thn) ctx)
                          (expand (m 'els) ctx))))))

(tip-extend! coret 'with-continuation-mark 'form
 (lambda (s ctx)
   (define m (match-syntax s '(with-continuation-mark key val body)))
   (freeze (rebuild s
                    (list (m 'with-continuation-mark)
                          (expand (m 'key) ctx)
                          (expand (m 'val) ctx)
                          (expand (m 'body) ctx))))))


(define (make-begin)
 (lambda (s ctx)
   (define m (match-syntax s '(begin-id e ...+)))
   (freeze (rebuild s
                    (cons (m 'begin-id)
                          (for/list ([e (in-list (m 'e))])
                            (expand e ctx)))))))

(tip-extend! coret 'begin 'form (make-begin))
(tip-extend! coret 'begin0 'form (make-begin))

(tip-extend! coret 'set! 'form
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
   (freeze (rebuild s
                    (list (literal 'set! ctx)
                          (m 'id)
                          (expand (m 'rhs) ctx))))))
