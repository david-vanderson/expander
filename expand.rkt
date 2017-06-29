#lang racket/base
(require racket/set
         racket/unit
         "syntax.rkt"
         "scope.rkt"
         "match.rkt"
         "namespace.rkt"
         "binding.rkt"
         "dup-check.rkt"
         "compile.rkt"
         "core.rkt"
         "expand-context.rkt")

(provide expand
         expand-body
         lookup
         
         expand+eval-for-syntaxes-binding
         eval-for-syntaxes-binding
         eval-for-bindings
         
         rebuild)

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
   [else
    ;; Variable or form as identifier macro
    (dispatch (lookup binding ctx s) s ctx)]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s ctx)
  (define id (car (syntax-e s)))
  (define binding (resolve id (expand-context-phase ctx)))
  (cond
   [(not binding)
    ;; The `#%app` binding might do something with unbound ids
    (expand-implicit '#%app s ctx)]
   [else
    ;; Find out whether it's bound as a variable, syntax, or core form
    (define t (lookup binding ctx id))
    (cond
     [(variable? t)
      ;; Not as syntax or core form, so use implicit `#%app`
      (expand-implicit '#%app s ctx)]
     [else
      ;; Syntax or core form as "application"
      (dispatch t s ctx)])]))
  
;; Handle an implicit: `#%app`, `#%top`, or `#%datum`
(define (expand-implicit sym s ctx)
  (define id (datum->syntax s sym))
  ;; Instead of calling `expand` with a new form that starts `id`,
  ;; we implement the "applicaiton"-form case of `expand` so that
  ;; we provide an error if the implicit form is not suitably bound
  (define b (resolve id (expand-context-phase ctx)))
  (define t (and b (lookup b ctx id)))
  (cond
   [(core-form? t)
    (if (expand-context-only-immediate? ctx)
        s
        (dispatch t (datum->syntax s (cons sym s) s) ctx))]
   [(transformer? t)
    (dispatch t (datum->syntax s (cons sym s) s) ctx)]
   [else
    (error (format "no transformer binding for ~a:" sym)
           s)]))

;; Expand `s` given that the value `t` of the relevant binding,
;; where `t` is either a core form, a macro transformer, some
;; other compile-time value (which is an error), or a token
;; indincating that the binding is a run-time variable
(define (dispatch t s ctx)
  (cond
   [(core-form? t)
    (if (expand-context-only-immediate? ctx)
        s
        ((core-form-expander t) s ctx))]
   [(transformer? t)
    ;; Apply transformer and expand again
    (expand (apply-transformer t s ctx) ctx)]
   [(variable? t)
    ;; A reference to a variable expands to itself
    s]
   [else
    ;; Some other compile-time value:
    (error "illegal use of syntax:" t)]))

;; Given a macro transformer `t`, apply it --- adding appropriate
;; scopes to represent the expansion step
(define (apply-transformer t s ctx)
  ;; Make a unique mark for this transformer application
  (define m (gensym 't))
  ;; Mark syntax going in
  (define marked-s (mark s m))
  ;; Call the transformer
  (define transformed-s (t marked-s))
  (unless (syntax? transformed-s)
    (error "transformer produced non-syntax:" transformed-s))
  ;; Flip mark so it's only on introduced syntax
  (define result-s (mark transformed-s m))
  result-s)


;; Helper to lookup a binding in an expansion context
(define (lookup b ctx id)
  (binding-lookup b
                  (expand-context-env ctx)
                  (expand-context-namespace ctx)
                  id))

;; ----------------------------------------

;; Expand a sequence of body forms in a definition context
(define (expand-body bodys s ctx)
  ;; Create an expansion context for expanding only immediate macros;
  ;; this partial-expansion phase uncovers macro- and variable
  ;; definitions in the definition context
  (define body-ctx (struct-copy expand-context ctx
                                [only-immediate? #t]))

  ;; Make and save a handle to new branches
  (define branchid (gensym 'def))  ; def for definition context
  (define newbranches (make-newbranches))
  (set! bodys (extend-branch bodys branchid newbranches))
  
  (let loop ([body-ctx body-ctx]
             [bodys bodys]
             [done-bodys null] ; accumulated expressions
             [val-binds null]  ; accumulated bindings
             [dups (make-check-no-duplicate-table)])
    (cond
     [(null? bodys)
      ;; Partial expansion is complete, so finish by rewriting to
      ;; `letrec-values`
      (finish-expanding-body body-ctx done-bodys val-binds s)]
     [else
      (define exp-body (expand (car bodys) body-ctx))

      ;; expand could add macro-introduced syntax into the definition context
      ;; that we need to add a branch to
      (set! exp-body (extend-branch exp-body branchid newbranches))

      ;; the partial expand means exp-body will be one of:
      ;; - an identifier that is a variable, primitive, or core form
      ;; - a list where the first identifier is a core form
      (case (core-form-sym exp-body (expand-context-phase body-ctx))
        [(begin)
         ;; Splice a `begin` form
         (define m (match-syntax exp-body '(begin e ...)))
         (loop body-ctx
               (append (m 'e) (cdr bodys))
               done-bodys
               val-binds
               dups)]
        [(define-values)
         ;; Found a variable definition; add bindings, extend the
         ;; environment, and continue
         (define m (match-syntax exp-body '(define-values (id ...) rhs)))
         (define ids (m 'id))
         (define new-dups (check-no-duplicate-ids ids exp-body dups))
         (define keys (for/list ([id (in-list ids)])
                        (define key (gensym (syntax-e id)))
                        (define b (local-binding key))
                        (add-binding! id (syntax-e id)
                                      (expand-context-phase body-ctx)
                                      b newbranches)
                        key))
         (define extended-env (for/fold ([env (expand-context-env body-ctx)]) ([key (in-list keys)])
                                (env-extend env key variable)))
         (loop (struct-copy expand-context body-ctx
                            [env extended-env])
               (cdr bodys)
               null
               (cons (list ids (m 'rhs))
                     ;; If we had accumulated some expressions, we
                     ;; need to turn each into a
                     ;;  (defined-values () (begin <expr> (values)))
                     ;; form so it can be kept with definitions to
                     ;; preserved order
                     (append
                      (for/list ([done-body (in-list done-bodys)])
                        (no-binds done-body s (expand-context-phase body-ctx)))
                      val-binds))
               new-dups)]
        [(define-syntaxes)
         ;; Found a macro definition; add bindings, evaluate the
         ;; compile-time right-hand side, install the compile-time
         ;; values in the environment, and continue
         (define m (match-syntax exp-body '(define-syntaxes (id ...) rhs)))
         (define ids (m 'id))
         (define new-dups (check-no-duplicate-ids ids exp-body dups))
         (define keys (for/list ([id (in-list ids)])
                        (define key (gensym (syntax-e id)))
                        (define b (local-binding key))
                        (add-binding! id (syntax-e id)
                                      (expand-context-phase body-ctx)
                                      b newbranches)
                        key))
         (define vals (eval-for-syntaxes-binding (m 'rhs) ids ctx))
         (define extended-env (for/fold ([env (expand-context-env body-ctx)]) ([key (in-list keys)]
                                                                               [val (in-list vals)])
                                (env-extend env key val)))
         (loop (struct-copy expand-context body-ctx
                            [env extended-env])
               (cdr bodys)
               done-bodys
               val-binds
               new-dups)]
        [else
         ;; Found an expression; accumulate it and continue
         (loop body-ctx
               (cdr bodys)
               (cons exp-body done-bodys)
               val-binds
               dups)])])))

;; Partial expansion is complete, so assumble the result as a
;; `letrec-values` form and continue expanding
(define (finish-expanding-body body-ctx done-bodys val-binds s)
  (when (null? done-bodys)
    (error "no body forms:" s))
  ;; As we finish expanding, we're no longer in a definition context
  (define finish-ctx (struct-copy expand-context body-ctx
                                  [only-immediate? #f]))
  ;; Helper to expand and wrap the ending expressions in `begin`, if needed:
  (define (finish-bodys)
    (cond
     [(null? (cdr done-bodys))
      (expand (car done-bodys) finish-ctx)]
     [else
      (datum->syntax
       #f
       `(,(core-literal 'begin (expand-context-phase finish-ctx))
         ,@(for/list ([body (in-list done-bodys)])
             (expand body finish-ctx)))
       s)]))
  (cond
   [(null? val-binds)
    ;; No definitions, so no `letrec-values` wrapper needed:
    (finish-bodys)]
   [else
    ;; Add `letrec-values` wrapper, finish expanding the right-hand
    ;; sides, and then finish the body expression:
    (datum->syntax
     #f
     `(,(core-literal 'letrec-values (expand-context-phase finish-ctx))
       ,(for/list ([bind (in-list (reverse val-binds))])
          `(,(datum->syntax #f (car bind)) ,(expand (cadr bind) finish-ctx)))
       ,(finish-bodys))
     s)]))

;; Helper to turn an expression into a binding clause with zero
;; bindings
(define (no-binds expr s phase)
  (list null (datum->syntax #f
                            `(,(core-literal 'begin phase)
                              ,expr
                              (,(core-literal '#%app phase)
                               ,(core-literal 'values phase)))
                            s)))

;; ----------------------------------------

;; Expand `s` as a compile-time expression relative to the current
;; expansion context
(define (expand-transformer s ctx)
  (define p (add1 (expand-context-phase ctx)))
  (expand (introduce s (core-branch p))
          (struct-copy expand-context ctx
                       [env empty-env]
                       [only-immediate? #f]
                       [phase p])))

;; Expand and evaluate `s` as a compile-time expression, ensuring that
;; the number of returned values matches the number of target
;; identifiers; return the expanded form as well as its values
(define (expand+eval-for-syntaxes-binding rhs ids ctx)
  (define exp-rhs (expand-transformer rhs ctx))
  (values exp-rhs
          (eval-for-bindings ids
                             exp-rhs
                             (add1 (expand-context-phase ctx))
                             (expand-context-namespace ctx))))

;; Expand and evaluate `s` as a compile-time expression, returning
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
