#lang racket

(provide expand
         compile
         (rename-out [eval-compiled eval])

         datum->syntax
         introduce)

;; We include tests to serve as examples of various functions work
(module+ test
  (require rackunit)
  (define (make-exn:fail? rx)
    (lambda (v)
      (and (exn:fail? v) (regexp-match? rx (exn-message v))))))

;; ----------------------------------------
;; Syntax objects

(struct syntax (e        ; a symbol
                mark     ; #t or #f to distinguish syntax introduced by a macro
                ehs)     ; list of envheads, one for each phase
        #:transparent)

;; For now, all syntax object are identifiers:
(define (identifier? s)
  (syntax? s))

(module+ test
  (check-equal? (identifier? (syntax 'x #f #f))
                #t))

;; The `datum->syntax` function coerces to syntax with the given envhead
;; leaving existing syntax as-is
(define (datum->syntax v [ctx #f])
  (cond
   [(syntax? v) v]
   [(symbol? v) (syntax v (and ctx (syntax-mark ctx)) (if ctx (syntax-ehs ctx) (list)))]
   [(list? v) (map (lambda (e) (datum->syntax e ctx)) v)]
   [else v]))

(module+ test
  (check-equal? (datum->syntax 'a)
                (syntax 'a #f (list)))
  (check-equal? (datum->syntax 1)
                1))


;; The `syntax->datum` function discards scopes --- immediate and
;; nested --- to produce a plain S-expression:
(define (syntax->datum s)
  (cond
   [(syntax? s) (syntax-e s)]
   [(list? s) (map syntax->datum s)]
   [else s]))

(module+ test
  (check-equal? (syntax->datum (datum->syntax 1))
                1)
  (check-equal? (syntax->datum (datum->syntax 'a))
                'a)
  (check-equal? (syntax->datum (datum->syntax '(a b c)))
                '(a b c)))


;; ----------------------------------------
;; Compile time environment tree

;; A binding is either:
;; a gensym for a local variable
;; symbol for a core form or primitive
;; procedure for macro

(struct env (id       ; a symbol
             binding  ; a binding
             prev)    ; pointer to previous env that this env extends
                      ; or #f if this is the first binding
  #:transparent)

;; syntax objects all point to an envhead
;; a binding form will insert an env into the front of the list
;; a macro invocation will make a new envhead branch
;; fully-expanded syntax copies this so it doesn't see new bindings

(struct envhead (id     ; unique id to reanimate introduced syntax
                 phase  ; integer
                 env)   ; pointer to first env
  #:transparent #:mutable)


(module+ test

  (define loc/a (gensym 'a))
  (define eh/a (envhead (gensym 'eh) 0 (env 'z (gensym 'z)
                                            (env 'a loc/a #f))))
  ;; Simulates
  ;;   (let ([a 1])
  ;;     (let ([z 2])
  ;;       ....))
  ;; where `a` is bound only once

  (define loc/b-out (gensym 'b))
  (define loc/b-in (gensym 'b))
  (define eh/b (envhead (gensym 'eh) 0 (env 'b loc/b-in
                                             (env 'b loc/b-out #f))))
  ;; Simulates
  ;;   (let ([b 1])
  ;;     (let ([b 2])
  ;;       ....))
  ;; where the inner `b` shadows the outer `b`
  
  (define loc/c (gensym 'c))
  (define loc/c-m (gensym 'c-m))
  (define loc/c-u (gensym 'c-u))
  (define env/before (env 'c-m loc/c-m #f))
  (define eh/c (envhead (gensym 'eh) 0 (env 'c loc/c env/before)))
  (define eh/c-u (envhead (gensym 'eh) 0 (env 'c loc/c-u env/before)))
  ;; Simulates
  ;      (let-syntax ((c-m (lambda (stx)  ; (c-m arg body) -> (let ((c arg)) body)
  ;                          (datum->syntax
  ;                           (cons (quote-syntax let)
  ;                            (cons (list (list (quote-syntax c) (car (cdr stx))))
  ;                             (cons (quote-syntax c)
  ;                              (cdr (cdr stx))))
  ;                           (syntax-envhead (car stx))))))
  ;        (let ([c 1])
  ;          (c-m 2
  ;            ....)))
  ;      =>
  ;        (let ([c 1])
  ;          (let ([c 2])
  ;            c)    ; from macro
  ;          c)      ; from body
  ;; where the inner c is from a macro, does not shadow
  )

(define (syntax-eh s phase)
  (findf (lambda (h) (= phase (envhead-phase h))) (syntax-ehs s)))

;; Finds the env for a given identifier; returns #f if the
;; identifier is unbound
(define (resolve id phase)
  (define eh (syntax-eh id phase))
  (if (not eh) (error "can't find an envhead for phase" phase) (void))
  (let loop ((e (envhead-env eh)))
    (cond
      ((not e)  ; ran out of envs
       #f)
      ((equal? (syntax-e id) (env-id e))  ; found it
       (env-binding e))
      (else
       (loop (env-prev e))))))


(module+ test
  (check-equal? (resolve (syntax 'a #f (list eh/a)) 0)
                loc/a)
  (check-equal? (resolve (syntax 'a #f (list eh/b)) 0)
                #f)
  (check-equal? (resolve (syntax 'zzz #f (list eh/a)) 0)
                #f)

  (check-equal? (resolve (syntax 'b #f (list eh/b)) 0)
                loc/b-in)
  (check-equal? (resolve (syntax 'zzz #f (list eh/b)) 0)
                #f)

  (check-equal? (resolve (syntax 'c #f (list eh/c)) 0)
                loc/c)
  (check-equal? (resolve (syntax 'c #f (list eh/c-u)) 0)
                loc/c-u)
  (check-equal? (resolve (syntax 'c-m #f (list eh/c)) 0)
                loc/c-m)
  (check-equal? (resolve (syntax 'c-m #f (list eh/c-u)) 0)
                loc/c-m))


;; add to this envhead's chain of bindings
(define (env-extend-binding! eh key val)
  (set-envhead-env! eh (env key val (envhead-env eh))))

;; remove most recent env in chain
(define (env-pop! eh)
  (set-envhead-env! eh (env-prev (envhead-env eh))))

;; make a new envhead so it doesn't get extended anymore
(define (eh-copy eh)
  (envhead (envhead-id eh) (envhead-phase eh) (envhead-env eh)))

;; copy all the envhead so this syntax won't be bound be future bindings
(define (freeze s)
  (cond
   [(syntax? s)
    (syntax (syntax-e s) (syntax-mark s) (map eh-copy (syntax-ehs s)))]
   [(list? s) (map freeze s)]
   [else s]))


;; ----------------------------------------
;; Core syntax and primitives

(define core-forms (seteq 'lambda 'let-syntax 'quote 'quote-syntax))
(define core-primitives (seteq 'datum->syntax 'syntax->datum 'syntax-e
                               'list 'cons 'car 'cdr 'map))

(define core-env
  (let ((eh (envhead #f #f #f)))
    (for ([sym (in-set (set-union core-forms core-primitives))])
      (env-extend-binding! eh sym sym))
    (envhead-env eh)))
  

(module+ test
  (define (eh/core) (envhead 'eh 0 core-env))
  (define (ehc) (list (eh/core))))


;; The `introduce` function adds all the core forms and primitives
;; to the empty environment and adds that envhead to all syntax
(define (introduce s (phase 0) (eh (envhead 'eh phase core-env)))
  (cond
    ((syntax? s) (syntax (syntax-e s) (syntax-mark s)
                         (if (syntax-eh s phase)
                             (error "already have an envhead for this phase" phase)
                             (cons eh (syntax-ehs s)))))
    ((list? s) (map (lambda (v) (introduce v phase eh)) s))
    (else s)))


(module+ test
  (check-equal? (resolve (datum->syntax 'lambda (syntax 'zzz #f (list (envhead #f 0 #f)))) 0)
                #f)
  (check-equal? (resolve (introduce (datum->syntax 'lambda)) 0)
                'lambda)) ; i.e., the core `lambda` form


(define (mark v)
  (cond
   [(syntax? v) (syntax (syntax-e v) #t (syntax-ehs v))]
   [(list? v) (map mark v)]
   [else v]))

(define (branch-introduced v phase)
  (define ehh (make-hash))
  (let branch-introduced* ((v v))
    (cond
      [(and (syntax? v) (not (syntax-mark v)))
       ; introduced syntax, branch
       (define eh (syntax-eh v phase))
       (if (not eh) (error "can't find an envhead for phase" phase) (void))
       
       (define neweh (hash-ref ehh (envhead-id eh) #f))
       (begin
         (cond
           [neweh (void)]
           [else
            (set! neweh (envhead (gensym 'eh) phase (envhead-env eh)))
            ; map old id to new eh
            (hash-set! ehh (envhead-id eh) neweh)])
         (printf "branching adding ~a to ~a\n" (envhead-id neweh) (syntax-e v))
         (syntax (syntax-e v) #f (cons neweh (remove eh (syntax-ehs v)))))]
      [(list? v) (map branch-introduced* v)]
      [else v])))


;; ----------------------------------------
;; Expansion Dispatch

(module+ test
  ;; Examples to demonstrate `expand`

  ;; Binding and using a macro:
  (check-equal? (syntax->datum
                 (expand (introduce
                          (datum->syntax
                           '(let-syntax ([one (lambda (stx)
                                                (quote-syntax '1))])
                             (one))))))
                '(quote 1))

  ;; A `(lambda (x) x)` form expands to itself, as long as it has the scope
  ;; used to bind all core-forms:
  (check-equal? (syntax->datum
                 (expand (introduce (datum->syntax '(lambda (x) x)))))
                '(lambda (x) x))
  
  ;; A reference to a core primitive expands to itself:
  (check-equal? (expand (introduce (syntax 'cons #f (list))))
                (syntax 'cons #f (ehc)))
  
  ;; A locally-bound variable expands to itself:
  (check-equal? (expand (syntax 'a #f (list eh/a))) ; bound to `loc1` above
                (syntax 'a #f (list eh/a)))
  
  ;; A free variable triggers an error:
  (check-exn (make-exn:fail? "free variable")
             (lambda ()
               (expand (syntax 'a #f (list (envhead 'eh 0 #f))))))
  
  ;; Application of a locally-bound variable to a number quotes the
  ;; number argument expression:
  (let [(eh (eh/core))]
    (env-extend-binding! eh 'a loc/a)
    (env-extend-binding! eh 'z (gensym 'z))
    (check-equal? (expand (list (syntax 'a #f (list eh))
                                (list (syntax 'quote #f (list eh)) 1)))
                  (list (syntax 'a #f (list eh))
                        (list (syntax 'quote #f (list eh))
                              1))))

  ;; Application of a number to a number expands to an application
  ;; (but will be a run-time error if evaluated):
  (check-equal? (expand (introduce
                         (datum->syntax '('0 '1))))
                (list (list (syntax 'quote #f (list (envhead 'eh 0 core-env)))
                            0)
                      (list (syntax 'quote #f (list (envhead 'eh 0 core-env)))
                            1)))
  
  ;; A locally-bound macro expands by applying the macro:
  (define ehc1 (ehc))
  (check-equal? (syntax->datum
                 (expand (list (syntax 'a #f (list (envhead 'eh 0 (env 'a (lambda (s)
                                                                            (list (syntax 'quote #f ehc1)
                                                                                  1)) core-env)))))))
                '(quote 1))
  (check-equal? (syntax->datum
                 (expand (datum->syntax '(a (lambda (x) x))
                                        (syntax 'zzz #f (list (envhead 'eh 0
                                                                       (env 'a (lambda (s) (list-ref s 1)) core-env)))))))
                '(lambda (x) x))
  )
;; Main expander entry point and loop:
(define (expand s (phase 0))
  (cond
   [(identifier? s)
    ;; An identifier by itself
    (expand-identifier s phase)]
   [(and (pair? s)
         (identifier? (car s)))
    ;; An "application" of an identifier; maybe a form or macro
    (expand-id-application-form s phase)]
   [(or (pair? s)
        (null? s))
    ;; An application form that doesn't start with an identifier
    (expand-app s phase)]
   [else
    (error "bad syntax:" s)]))

;; An identifier by itself:
(define (expand-identifier s phase)
  ;(printf "expand-identifier ~v\n" s)
  (define binding (resolve s phase))
  (cond
   [(not binding)
    (error "free variable:" s "in phase" phase)]
   [(set-member? core-primitives binding)
    (freeze s)]
   [(set-member? core-forms binding)
    (error "bad syntax:" s)]
   [else
    (freeze s)]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s phase)
  ;(printf "expand-id-app\n")
  (define id (car s))
  (define binding (resolve id phase))
  ;(printf "expand-id-app binding ~v\n" binding)
  (case binding
    [(lambda)
     ;(printf "expand-id-app lambda ~v\n" s)
     (expand-lambda s phase)]
    [(let-syntax)
     ;(printf "expand-id-app let-syntax ~v\n" s)
     (expand-let-syntax s phase)]
    [(quote quote-syntax)
     ;(printf "expand-id-app quotes ~v\n" s)
     (freeze s)]
    [else
     (cond
       [(procedure? binding)
        ;(printf "expand-id-app procedure ~v\n" s)
        ;; Apply transformer, then recur
        (expand (apply-transformer binding s phase))]
       [else
        ;(printf "expand-id-app app ~v\n" s)
        (expand-app s phase)])]))

;; Given a macro transformer `t`, apply it --- adding appropriate
;; scopes to represent the expansion step
(define (apply-transformer t s phase)
  ;; Mark given syntax
  (define marked-s (mark s))
  ;; Call the transformer
  ;(printf "before t: ~v\n\n" marked-s)
  (define t-s (t marked-s))
  ;(printf "after t: ~v\n\n" t-s)
  (define after-s (branch-introduced t-s phase))
  ;(printf "after b: ~v\n\n" after-s)
  after-s)

#;
(module+ test
  ;; Check that applying a macro transformer adds a scope to
  ;; introduced parts and leaves original parts alone:
  (define transformer
    (lambda (s)
       ;; This transformer converts `(_ f)` to `(f x)`
       (list (list-ref s 1)
             (datum->syntax 'x))))
  
  (define eh (envhead #f))
  (env-extend-binding! eh 'm transformer)
  (define transformed-s
    (apply-transformer
     transformer
     (list (syntax 'm #f eh)
           (syntax 'f #f eh))))
  
  (check-equal? (syntax->datum transformed-s)
                '(f x))
  (check-equal? (list-ref transformed-s 0)
                (syntax 'f #f (env-branch (syntax 'm #f eh)))))

;; ----------------------------------------

(define (expand-lambda s phase)
  ;(printf "expand-lambda ~v\n" s)
  (match-define `(,lambda-id (,arg-id) ,body) s)
  (set! lambda-id (freeze lambda-id))
  ;; Get the env branch from the binding variable
  (define eh (syntax-eh arg-id phase))
  (if (not eh) (error "can't find an envhead for phase" phase) (void))
  (define sym (syntax-e arg-id))
  ;; Add the new binding
  (env-extend-binding! eh sym (gensym sym))
  ;; Freeze env chain on arg-id
  (set! arg-id (freeze arg-id))  ;; probably don't need this
  ;; Expand the function body:
  (define exp-body (expand body phase))
  ;; Remove the new binding
  (env-pop! eh)
  (list lambda-id (list arg-id) exp-body))

(define (expand-let-syntax s phase)
  ;(printf "expand-let-syntax ~v\n" s)
  (match-define `(,let-syntax-id ([,lhs-id ,rhs])
                    ,body)
                s)
  (set! let-syntax-id (freeze let-syntax-id))
  ;; Evaluate compile-time expressions:
  (define rhs-val (eval-for-syntax-binding rhs (+ phase 1)))
  ;; Get the env branch from the binding variable
  (define eh (syntax-eh lhs-id phase))
  (if (not eh) (error "can't find an envhead for phase" phase) (void))
  (define sym (syntax-e lhs-id))
  ;; Add the new binding
  (env-extend-binding! eh sym rhs-val)
  (set! lhs-id (freeze lhs-id))
  ;; Expand body
  (define exp-body (expand body phase))
  ;; Remove the new binding
  (env-pop! eh)
  exp-body)

;; Expand an application (i.e., a function call)
(define (expand-app s phase)
  (map (lambda (sub-s) (expand sub-s phase)) s))

;; ----------------------------------------

;; Expand and evaluate `rhs` as a compile-time expression
(define (eval-for-syntax-binding rhs phase)
  (define expanded-rhs (expand (introduce rhs phase) phase))
  ;(write expanded-rhs)
  ;(newline)
  (define compiled-rhs (compile expanded-rhs phase))
  ;(write compiled-rhs)
  ;(newline)
  (eval-compiled compiled-rhs))


(module+ test
  (check-equal? (eval-for-syntax-binding (datum->syntax
                                          '(car (list '1 '2))) 1)
                1)
  
  (check-equal? ((eval-for-syntax-binding (datum->syntax
                                           '(lambda (x) (syntax-e x))) 1)
                 (syntax 'x #f #f))
                'x))

;; ----------------------------------------

;; Convert an expanded syntax object to an expression that is
;; represented by a plain S-expression.
(define (compile s (phase 0))
  (cond
   [(pair? s)
    (define core-sym (and (identifier? (car s))
                          (resolve (car s) phase)))
    (case core-sym
      [(lambda)
       (match-define `(,lambda-id (,id) ,body) s)
       `(lambda (,(resolve id phase)) ,(compile body phase))]
      [(quote)
       (match-define `(,quote-id ,datum) s)
       ;; Strip away scopes:
       `(quote ,(syntax->datum datum))]
      [(quote-syntax)
       (match-define `(,quote-syntax-id ,datum) s)
       ;; Preserve the complete syntax object:
       `(quote ,datum)]
      [else
       ;; Application:
       (map (lambda (v) (compile v phase)) s)])]
   [(identifier? s)
    (resolve s phase)]
   [else
    (error "bad syntax after expansion:" s)]))

;; Using the host Racket system: create a fresh namespace for
;; evaluating expressions that have been `expand`ed and `compile`d,
;; and install the expander's `datum->syntax` and `syntax-e`
;; to replace the host primitives
(define namespace (make-base-namespace))
(namespace-set-variable-value! 'datum->syntax datum->syntax #t namespace)
(namespace-set-variable-value! 'syntax->datum syntax->datum #t namespace)
(namespace-set-variable-value! 'syntax-e syntax-e #t namespace)

(define (eval-compiled s)
  (eval s namespace))
