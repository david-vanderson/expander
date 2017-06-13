#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         ;"namespace.rkt"
         ;"dup-check.rkt"
         "compile.rkt"
         ;"core.rkt"
         "expand-context.rkt"
         )

(provide expand
         expand-body
         
         expand+eval-for-syntaxes-binding
         eval-for-syntaxes-binding
         eval-for-bindings

         literal
         rebuild)


;; helper to create an identifier that always refers to the core form
(define (literal sym ctx)
  (define phase (expand-context-phase ctx))
  (introduce (datum->syntax #f sym)
             phase
             (expand-context-coreb ctx)))

;; ----------------------------------------

(define (expand s ctx)
  (cond
   [(identifier? s)
    (expand-identifier s ctx)]
   [(and (pair? (syntax-e s))
         (identifier? (car (syntax-e s))))
    (expand-id-application-form s ctx)]
   [(or (pair? (syntax-e s))
        (null? (syntax-e s)))
    ;; An "application" form that doesn't start with an identifier, so
    ;; use implicit `#%app`
    (expand-implicit '#%app s ctx)]
   [else
    ;; Anything other than an identifier or parens triggers the
    ;; implicit `#%datum` form
    (expand-implicit '#%datum s ctx)]))

;; An identifier by itself:
(define (expand-identifier s ctx)
  (define binding (resolve s (expand-context-phase ctx)))
  (cond
   [(not binding)
    ;; The implicit `#%top` form handles unbound identifiers
    (expand-implicit '#%top s ctx)]
   [(or (equal? 'prim (bind-type binding))
        (equal? 'var (bind-type binding)))
    s]
   [(equal? 'form (bind-type binding))
    (if (expand-context-only-immediate? ctx)
        s
        ((bind-val binding) s ctx))]
   [(equal? 'stx (bind-type binding))
    (if (procedure? (bind-val binding))
        (expand (apply-transformer (bind-val binding) s) ctx)
        (error "illegal use of syntax:" s))]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s ctx)
  (define id (car (syntax-e s)))
  (define binding (resolve id (expand-context-phase ctx)))
  (cond
   [(or (not binding)
        (equal? 'var (bind-type binding))
        (equal? 'prim (bind-type binding)))
    (expand-implicit '#%app s ctx)]
   [(equal? 'form (bind-type binding))
    (if (expand-context-only-immediate? ctx)
        s
        ((bind-val binding) s ctx))]
   [(equal? 'stx (bind-type binding))
    (if (procedure? (bind-val binding))
        (expand (apply-transformer (bind-val binding) s) ctx)
        (error "illegal use of syntax:" s))]))
  
;; Handle an implicit: `#%app`, `#%top`, or `#%datum`
(define (expand-implicit sym s ctx)
  (define id (datum->syntax s sym s s))
  (define b (resolve id (expand-context-phase ctx)))
  (cond
   [(and b (equal? 'form (bind-type b)))
    (if (expand-context-only-immediate? ctx)
        s
        (expand (datum->syntax s (cons id s) s s) ctx))]
   [(and b
         (equal? 'stx (bind-type b))
         (procedure? (bind-val b)))
    (expand (apply-transformer (bind-val b) (datum->syntax s (cons id s) s s)) ctx)]
   [else
    (error (format "no transformer binding for ~a:" sym)
           s)]))

;; Given a macro transformer `t`, apply it --- adding appropriate
;; scopes to represent the expansion step
(define (apply-transformer t s)
  ;; Mark given syntax
  (define m (gensym 't))
  (define marked-s (mark-pre s m))
  ;; Call the transformer
  ;(printf "before t: ~v\n\n" marked-s)
  (define transformed-s (t marked-s))
  (unless (syntax? transformed-s)
    (error "transformer produced non-syntax:" transformed-s))
  ;(printf "after t: ~v\n\n" t-s)
  (define after-s (mark-post transformed-s m))
  ;(printf "after b: ~v\n\n" after-s)
  after-s)

;; ----------------------------------------

;; Expand a sequence of body forms in a definition context
(define (expand-body s bodys ctx)
  ;; Create an expansion context for expanding only immediate macros;
  ;; this partial-expansion phase uncovers macro- and variable
  ;; definitions in the definition context
  (define body-ctx (struct-copy expand-context ctx
                                [only-immediate? #t]))
  (define defid (gensym 'def))

  (set! bodys (extend-branch bodys defid (expand-context-phase ctx)))

  (let loop ([bodys bodys]
             [done-trans null]  ; accumulated expanded transformers
             [done-bodys null]  ; accumulated expressions
             [val-binds null])  ; accumulated bindings
    (cond
     [(null? bodys)
      ;; Partial expansion is complete, so finish by rewriting to
      ;; `letrec-values`
      (finish-expanding-body ctx done-bodys val-binds s)]
     [else
      (define exp-body (expand (car bodys) body-ctx))
      ;; because of the partial expand, exp-body will be:
      ;; a list where the first identifier is a core form
      ;; an identifier that is a variable, primitive, or core form
      (define id (if (pair? (syntax-e exp-body))
                     (car (syntax-e exp-body))
                     exp-body))
      ;(printf "resolving ~v\n\n" id)
      (define b (resolve id (expand-context-phase ctx)))
      (cond
        [(or (not b)  ; var we haven't found the binding to yet
             (equal? 'var (bind-type b))
             (equal? 'prim (bind-type b)))
         ;(printf "var/prim ~v\n\n" exp-body)
         ;; Found a var or primitive; accumulate it and continue
         (loop (cdr bodys)
               done-trans
               (append done-bodys (list exp-body))
               val-binds)]
        [else
         (case (syntax-e id)
           [(begin)
            ;; Splice a `begin` form
            ;(printf "splicing begin\n\n")
            (define m (match-syntax exp-body '(begin e ...)))
            (loop (append (m 'e) (cdr bodys))
                  done-trans
                  done-bodys
                  val-binds)]
           [(define-values)
            ;; Found a variable definition
            (define m (match-syntax exp-body '(define-values (id ...) rhs)))
            (for ([id (in-list (m 'id))])
              (define sym (syntax-e id))
              (define b (bind sym 'var (gensym sym)))
              ;; Add the new binding
              ;(printf "define-values binding ~a\n\n" sym)
              (add-binding! (cdr bodys) id b defid (expand-context-phase ctx))
              (add-binding! exp-body id b defid (expand-context-phase ctx))
              (add-binding! done-trans id b defid (expand-context-phase ctx))
              (add-binding! done-bodys id b defid (expand-context-phase ctx))
              (add-binding! val-binds id b defid (expand-context-phase ctx)))
              
            (loop (cdr bodys)
                  done-trans
                  null
                  (append val-binds
                        ;; If we had accumulated some expressions, we
                        ;; need to turn each into a
                        ;;  (defined-values () (begin <expr> (values)))
                        ;; form so it can be kept with definitions to
                        ;; preserved order
                          (for/list ([done-body (in-list done-bodys)])
                            (no-binds done-body s ctx))
                          (list (list (m 'id) (m 'rhs)))))]
           [(define-syntaxes)
            ;(printf "define-syntaxes\n\n")
            ;; Found a macro definition, this is the tricky one
            ;; We have to expand+eval the definition in case a further use
            ;; expands to more defines in this same definition context.
            ;; But the macro-introduced syntax can also be bound by definitions
            ;; we haven't seen yet.
            (define m (match-syntax exp-body '(define-syntaxes (id ...) rhs)))
            (for ([id (in-list (m 'id))])
              (define sym (syntax-e id))
              (define b (bind sym 'stx #f))
              ;; Add the new binding
              ;(printf "define-syntaxes binding ~a\n\n" sym)
              (add-binding! (cdr bodys) id b defid (expand-context-phase ctx))
              (add-binding! exp-body id b defid (expand-context-phase ctx))
              (add-binding! done-trans id b defid (expand-context-phase ctx))
              (add-binding! done-bodys id b defid (expand-context-phase ctx))
              (add-binding! val-binds id b defid (expand-context-phase ctx)))

            ;(printf "define-syntaxes (m 'rhs) ~v\n\n" (m 'rhs))
            (define-values (exp-trans transformers)
              (expand+eval-for-syntaxes-binding (m 'rhs) (m 'id) ctx))
            
            ;(printf "define-syntaxes exp-trans ~v\n\n" exp-trans)
            
            ;; patch up the placeholder
            (for ([id (in-list (m 'id))]
                  [trans (in-list transformers)])
              (define binding (resolve id (expand-context-phase ctx) #t))
              (set-bind-val! binding trans))
            
            (loop (cdr bodys)
                  (cons exp-trans done-trans)
                  done-bodys
                  val-binds)]
           [else
            ;(printf "expression ~v\n\n" exp-body)
            ;; Found an expression; accumulate it and continue
            (loop (cdr bodys)
                  done-trans
                  (append done-bodys (list exp-body))
                  val-binds)])])])))

;; Partial expansion is complete, so assumble the result as a
;; `letrec-values` form and continue expanding
(define (finish-expanding-body ctx done-bodys val-binds s)
  (when (null? done-bodys)
    (error "definition context didn't end with expression:" s))
  
  ;; Helper to expand and wrap the ending expressions in `begin`, if needed:
  (define (finish-bodys)
    (cond
     [(null? (cdr done-bodys))      
      (expand (car done-bodys) ctx)]
     [else
      (rebuild s
               `(,(literal 'begin ctx)
                 ,@(for/list ([body (in-list done-bodys)])
                     (expand body ctx))))]))

  (define exp-bodys
    (cond
      [(null? val-binds)
       ;; No definitions, so no `letrec-values` wrapper needed:
       (finish-bodys)]
      [else
       ;; Add `letrec-values` wrapper, finish expanding the right-hand
       ;; sides, and then finish the body expression:
       (rebuild s
                `(,(literal 'letrec-values ctx)
                  ,(for/list ([bind (in-list val-binds)])
                     `(,(datum->syntax #f (car bind)) ,(expand (cadr bind) ctx)))
                  ,(finish-bodys)))]))

  exp-bodys)

;; Helper to turn an expression into a binding clause with zero
;; bindings
(define (no-binds expr s ctx)
  (list null (datum->syntax #f
                            `(,(literal 'begin ctx)
                              ,expr
                              (,(literal '#%app ctx)
                               ,(literal 'values ctx)))
                            s)))


;; ----------------------------------------

;; Expand `s` as a compile-time expression relative to the current
;; expansion context
(define (expand-transformer s ctx)
  (define phase (+ (expand-context-phase ctx) 1))
  (define ss (introduce s phase (expand-context-coreb ctx)))
  ;(printf "expand-transformer ss ~v\n\n" ss)
  (define sss (expand ss
                      (struct-copy expand-context ctx
                                   [phase phase])))
  ;(printf "expand-transformer sss ~v\n\n" sss)
  sss)

;; Expand and evaluate `rhs` as a compile-time expression, ensuring that
;; the number of returned values matches the number of target
;; identifiers; return the expanded form as well as its values
(define (expand+eval-for-syntaxes-binding rhs ids ctx)
  (define exp-rhs (expand-transformer rhs ctx))
  (values exp-rhs
          (eval-for-bindings ids
                             exp-rhs
                             (+ (expand-context-phase ctx) 1)
                             (expand-context-namespace ctx))))

;; Expand and evaluate `rhs` as a compile-time expression, returning
;; only the compile-time values
(define (eval-for-syntaxes-binding rhs ids ctx)
  (define-values (exp-rhs vals)
    (expand+eval-for-syntaxes-binding rhs ids ctx))
  vals)

;; Expand and evaluate `s` as an expression in the given phase;
;; ensuring that the number of returned values matches the number of
;; target identifiers; return the values
(define (eval-for-bindings ids s phase ns)
  (define compiled (compile s phase ns))
  (define vals
    (call-with-values (lambda () (expand-time-eval `(#%expression ,compiled)))
      list))
  (unless (= (length vals) (length ids))
    (error "wrong number of results (" (length vals) "vs." (length ids) ")"
           "from" s))
  vals)


;; ----------------------------------------
;; A helper for forms to reconstruct syntax
(define (rebuild orig-s new)
  (datum->syntax orig-s new orig-s orig-s))