#lang racket
;(require "match.rkt")

(provide expand
         compile
         (rename-out [eval-compiled eval])

         datum->syntax
         namespace-syntax-introduce)

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
;; type 'var val is gensym for a local variable
;; type 'form val is symbol for a core form
;; type 'prim val is symbol for core primitive
;; type 'stx val is procedure for macro
;; type 'stx with not a procedure is a syntax error

(struct bind (type val) #:transparent)

(struct env (id         ; a symbol
             binding    ; a bind struct
             prev)      ; pointer to previous env that this env extends
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


;; If identifiers are `bound-identifier=?`, they are fully
;; interchangable: same symbol and same binding branch
(define (bound-identifier=? a b phase)
  (and (eq? (syntax-e a) (syntax-e b))
       (let ()
         (define eha (syntax-eh a phase))
         (if (not eha) (error "can't find an eha for phase" phase) (void))
         (define ehb (syntax-eh b phase))
         (if (not ehb) (error "can't find an ehb for phase" phase) (void))
         (eq? eha ehb))))


(module+ test

  (define loc/a (gensym 'a))
  (define eh/a (envhead (gensym 'eh/a) 0 (env 'z (bind 'var (gensym 'z))
                                              (env 'a (bind 'var loc/a) #f))))
  ;; Simulates
  ;;   (let ([a 1])
  ;;     (let ([z 2])
  ;;       ....))
  ;; where `a` is bound only once

  (define loc/b-out (gensym 'b))
  (define loc/b-in (gensym 'b))
  (define eh/b (envhead (gensym 'eh) 0 (env 'b (bind 'var loc/b-in)
                                             (env 'b (bind 'var loc/b-out) #f))))
  ;; Simulates
  ;;   (let ([b 1])
  ;;     (let ([b 2])
  ;;       ....))
  ;; where the inner `b` shadows the outer `b`

  (check-equal? (bound-identifier=? (syntax 'a #f (list eh/a))
                                    (syntax 'a #f (list eh/a)) 0)
                #t)
  (check-equal? (bound-identifier=? (syntax 'a #f (list eh/a))
                                    (syntax 'z #f (list eh/a)) 0)
                #f)
  (check-equal? (bound-identifier=? (syntax 'a #f (list eh/a))
                                    (syntax 'a #f (list eh/b)) 0)
                #f)
  
  (define loc/c (gensym 'c))
  (define loc/c-m (lambda (x) x))
  (define loc/c-u (gensym 'c-u))
  (define env/before (env 'c-m (bind 'stx loc/c-m) #f))
  (define eh/c (envhead (gensym 'eh) 0 (env 'c (bind 'var loc/c) env/before)))
  (define eh/c-u (envhead (gensym 'eh) 0 (env 'c (bind 'var loc/c-u) env/before)))
  ;; Simulates
  ;      (let-syntax ((c-m (lambda (stx)  ; (c-m arg body) -> (let ((c arg)) body)
  ;                          (datum->syntax
  ;                           (cons (quote-syntax let)
  ;                            (cons (list (list (quote-syntax c) (car (cdr stx))))
  ;                             (cons (quote-syntax c)
  ;                              (cdr (cdr stx))))
  ;
  ;        (let ([c 1])
  ;          (c-m 2
  ;            c)))
  ;      =>
  ;        (let ([c 1])
  ;          (let ([c 2])
  ;            c    ; from macro
  ;            c)   ; from body
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
  (check-equal? (bind-val (resolve (syntax 'a #f (list eh/a)) 0))
                loc/a)
  (check-equal? (resolve (syntax 'a #f (list eh/b)) 0)
                #f)
  (check-equal? (resolve (syntax 'zzz #f (list eh/a)) 0)
                #f)

  (check-equal? (bind-val (resolve (syntax 'b #f (list eh/b)) 0))
                loc/b-in)
  (check-equal? (resolve (syntax 'zzz #f (list eh/b)) 0)
                #f)

  (check-equal? (bind-val (resolve (syntax 'c #f (list eh/c)) 0))
                loc/c)
  (check-equal? (bind-val (resolve (syntax 'c #f (list eh/c-u)) 0))
                loc/c-u)
  (check-equal? (bind-val (resolve (syntax 'c-m #f (list eh/c)) 0))
                loc/c-m)
  (check-equal? (bind-val (resolve (syntax 'c-m #f (list eh/c-u)) 0))
                loc/c-m))


;; add to this envhead's chain of bindings
(define (env-extend-binding! eh id bind)
  (set-envhead-env! eh (env id bind (envhead-env eh))))

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


  
;; Determine whether two identifiers have the same binding
(define (free-identifier=? a b phase)
  (eq? (resolve a phase) (resolve b phase)))

(module+ test
  (check-equal? (free-identifier=? (syntax 'c-m #f (list eh/c))
                                   (syntax 'c-m #f (list eh/c-u)) 0)
                #t)
  (check-equal? (free-identifier=? (syntax 'c #f (list eh/c))
                                   (syntax 'c #f (list eh/c-u)) 0)
                #f))

;; ----------------------------------------
;; Core syntax and primitives

(define core-forms (seteq 'lambda 'let-syntax '#%app 'quote 'quote-syntax))
(define core-primitives (seteq 'datum->syntax 'syntax->datum 'syntax-e
                               'list 'cons 'car 'cdr 'map))

(define core-env
  (let ((eh (envhead #f #f #f)))
    (for ([sym (in-set core-primitives)])
      (env-extend-binding! eh sym (bind 'prim sym)))
    (for ([sym (in-set core-forms)])
      (env-extend-binding! eh sym (bind 'form sym)))
    (envhead-env eh)))
  

(module+ test
  (define (eh/core) (envhead 'eh 0 core-env))
  (define (ehc) (list (eh/core))))


;; The `introduce` function adds all the core forms and primitives
;; to the empty environment and adds that envhead to all syntax
(define (namespace-syntax-introduce s (phase 0) (eh (envhead 'eh phase core-env)))
  (cond
    ((syntax? s) (syntax (syntax-e s) (syntax-mark s)
                         (if (syntax-eh s phase)
                             (error "already have an envhead for this phase" phase)
                             (cons eh (syntax-ehs s)))))
    ((list? s) (map (lambda (v) (namespace-syntax-introduce v phase eh)) s))
    (else s)))


(module+ test
  (check-equal? (resolve (datum->syntax 'lambda (syntax 'zzz #f (list (envhead #f 0 #f)))) 0)
                #f)
  (check-equal? (bind-val (resolve (namespace-syntax-introduce (datum->syntax 'lambda)) 0))
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
      [(and (syntax? v) (syntax-mark v))
       ; not introduced, just reset mark
       ; this is not necessary but helpful for testing
       (syntax (syntax-e v) #f (syntax-ehs v))]
      [(list? v) (map branch-introduced* v)]
      [else v])))


;; ----------------------------------------
;; Expansion Dispatch

(module+ test
  ;; Examples to demonstrate `expand`
  
  ;; A number expands to a `quote` form:
  (check-equal? (syntax->datum (expand (namespace-syntax-introduce (datum->syntax 1))))
                '(quote 1))

  ;; Binding and using a macro:
  (check-equal? (syntax->datum
                 (expand (namespace-syntax-introduce
                          (datum->syntax
                           '(let-syntax ([one (lambda (stx)
                                                (quote-syntax '1))])
                             (one))))))
                '(quote 1))

  ;; A `(lambda (x) x)` form expands to itself, as long as it has the scope
  ;; used to bind all core-forms:
  (check-equal? (syntax->datum
                 (expand (namespace-syntax-introduce (datum->syntax '(lambda (x) x)))))
                '(lambda (x) x))
  
  ;; A reference to a core primitive expands to itself:
  (check-equal? (expand (namespace-syntax-introduce (syntax 'cons #f (list))))
                (syntax 'cons #f (ehc)))
  
  ;; A locally-bound variable expands to itself:
  (check-equal? (expand (syntax 'a #f (list eh/a))) ; bound to `loc1` above
                (syntax 'a #f (list eh/a)))
  
  ;; A free variable triggers an error:
  (check-exn (make-exn:fail? "free variable")
             (lambda ()
               (expand (syntax 'a #f (list (envhead 'eh 0 #f))))))
  
  ;; Application of a locally-bound variable to a number expands to an
  ;; `#%app` form and quotes the number
  (let [(eh (eh/core))]
    (define eh-old (envhead 'eh 0 (envhead-env eh)))
    (env-extend-binding! eh 'a (bind 'var loc/a))
    (check-equal? (expand (list (syntax 'a #f (list eh)) 1))
                  (list (syntax '#%app #f (list eh-old))
                        (syntax 'a #f (list eh))
                        (list (syntax 'quote #f (list eh-old))
                              1))))
  
  ;; A locally-bound macro expands by applying the macro:
  (let ((eh (eh/core)))
    (env-extend-binding! eh 'a (bind 'stx (lambda (s)
                                            (datum->syntax 1))))
    (check-equal? (syntax->datum
                   (expand (namespace-syntax-introduce (datum->syntax '(a)) 0 eh)))
                  '(quote 1)))

  (let ((eh (eh/core)))
    (env-extend-binding! eh 'a (bind 'stx (lambda (s) (list-ref s 1))))
    (check-equal? (syntax->datum
                   (expand (namespace-syntax-introduce (datum->syntax '(a (lambda (x) x))) 0 eh)))
                  '(lambda (x) x)))
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
    ;; Anything other than an identifier or parens is implicitly quoted,
    ;; so build a `quote` form
    ;; XXX introduce here is a hack, need to get the context
    ;; but can't get it from s because s might be just a number
    (list (namespace-syntax-introduce (datum->syntax 'quote) phase) s)]))

;; An identifier by itself:
(define (expand-identifier s phase)
  ;(printf "expand-identifier ~v\n" s)
  (define binding (resolve s phase))
  (if (not binding)
      (error "free variable:" s "in phase" phase)
      (void))
  
  (case (bind-type binding)
    [(form)
     (error "bad syntax:" s)]
    [(stx)
     (if (procedure? (bind-val binding))
         (expand (apply-transformer (bind-val binding) s phase))
         (error "illegal use of syntax:" s))]
    [else
     (freeze s)]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s phase)
  ;(printf "expand-id-app\n")
  (define id (car s))
  (define binding (resolve id phase))
  (if (not binding)
      (error "free variable:" s "in phase" phase)
      (void))
  ;(printf "expand-id-app binding ~v\n" binding)
  
  (case (bind-type binding)
    [(form)
     (case (bind-val binding)
       [(lambda)
        ;(printf "expand-id-app lambda ~v\n" s)
        (expand-lambda s phase)]
       [(let-syntax)
        (expand-let-syntax s phase)]
       [(#%app)
        (match-define (list app-id es ...) s)
        (expand-app es phase)]
       [(quote quote-syntax)
        ;(printf "expand-id-app quotes ~v\n" s)
        (freeze s)]
       [else
        (error "missed a core form in expand-id-application-form" (bind-val binding))])]
    [(stx)
     (if (procedure? (bind-val binding))
         (expand (apply-transformer (bind-val binding) s phase))
         (error "illegal use of syntax:" s))]
    [else
     ;(printf "expand-id-app app ~v\n" s)
     (expand-app s phase)]))

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

(module+ test
  ;; Check that applying a macro transformer branches the
  ;; introduced parts and leaves original parts alone:
  (let ((eh (eh/core)))
    (define t (lambda (s)
                ;; This transformer converts `(_ f)` to `(f x)`
                (list (list-ref s 1)
                      (datum->syntax 'x (syntax 'zzz #f (list eh))))))

  
    (env-extend-binding! eh 'm (bind 'stx t))
    (define transformed-s
      (apply-transformer t
                         (list (syntax 'm #f (list eh))
                               (syntax 'f #f (list eh))) 0))
  
    (check-equal? (syntax->datum transformed-s)
                  '(f x))
    (check-equal? (list-ref transformed-s 0)
                  (syntax 'f #f (list eh)))
    (check-not-equal? (list-ref transformed-s 1)
                      (syntax 'x #f (list eh)))
    )
  )

;; ----------------------------------------

(define (expand-lambda s phase)
  ;(printf "expand-lambda (~a) ~v\n\n" phase s)
  (match-define `(,lambda-id (,arg-ids ...) ,body) s)
  (set! lambda-id (freeze lambda-id))
  (define old-chains (list))
  (set! arg-ids
        (for/list ((arg-id arg-ids))
          ;; Get the env branch from the binding variable
          (define eh (syntax-eh arg-id phase))
          (if (not eh) (error "can't find an envhead for phase" phase) (void))
          (define sym (syntax-e arg-id))
          ;; Add the new binding
          (env-extend-binding! eh sym (bind 'var (gensym sym)))
          ;; save this old chain before we freeze so we can pop it later
          (set! old-chains (cons eh old-chains))
          ;; Freeze env chain on arg-id
          (freeze arg-id)))
  ;; Expand the function body:
  (define exp-body (expand body phase))
  ;; Remove the new bindings
  (for ((oc old-chains))
    (env-pop! oc))
  
  (list lambda-id arg-ids exp-body))

(define (expand-let-syntax s phase)
  ;(printf "expand-let-syntax ~v\n\n" s)
  (match-define `(,let-syntax-id ([,lhs-ids ,rhss] ...)
                    ,body)
                s)
  (set! let-syntax-id (freeze let-syntax-id))
  (for ((lhs-id lhs-ids) (rhs rhss))
    ;; Evaluate compile-time expressions:
    ;(printf "eval-for-syntax\n\n")
    (define rhs-val (eval-for-syntax-binding rhs (+ phase 1)))
    ;; Get the env branch from the binding variable
    ;(printf "syntax-eh\n\n")
    (define eh (syntax-eh lhs-id phase))
    (if (not eh) (error "can't find an envhead for phase" phase) (void))
    (define sym (syntax-e lhs-id))
    ;; Add the new binding
    (env-extend-binding! eh sym (bind 'stx rhs-val)))

  ;(printf "expanding body\n")
  ;; Expand body
  (define exp-body (expand body phase))
  
  ;; Remove the new bindings
  (for ((lhs-id lhs-ids))
    (define eh (syntax-eh lhs-id phase))
    (env-pop! eh))

  exp-body)

;; Expand an application (i.e., a function call)
(define (expand-app s phase)
  (match-define `(,rator ,rands ...) s)
  ;; Add `#%app` to make the application form explicit
  ;; XXX fix getting the context
  (list* (namespace-syntax-introduce (datum->syntax '#%app) phase)
         (expand rator phase)
         (map (lambda (rand) (expand rand phase))
              rands)))

;; ----------------------------------------

;; Expand and evaluate `rhs` as a compile-time expression
(define (eval-for-syntax-binding rhs phase)
  (define expanded-rhs (expand (namespace-syntax-introduce rhs phase) phase))
  ;(write expanded-rhs)
  ;(newline)
  ;(printf "compiling ~v\n\n" expanded-rhs)
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
    (define binding (resolve (car s) phase))
    (if (not (equal? (bind-type binding) 'form))
        (error "not a core form in expanded syntax:" s)
        (void))
    (case (bind-val binding)
      [(lambda)
       (match-define `(,lambda-id (,ids ...) ,body) s)
       `(lambda ,(map (lambda (id) (bind-val (resolve id phase))) ids) ,(compile body phase))]
      [(#%app)
       (match-define `(,app-id ,rator ,rands ...) s)
       (cons (compile rator phase) (map (lambda (rand) (compile rand phase)) rands))]
      [(quote)
       (match-define `(,quote-id ,datum) s)
       ;; Strip away scopes:
       `(quote ,(syntax->datum datum))]
      [(quote-syntax)
       (match-define `(,quote-syntax-id ,datum) s)
       ;; Preserve the complete syntax object:
       `(quote ,datum)]
      [else
       (error "unrecognized core form:" (bind-val binding))])]
   [(identifier? s)
    (bind-val (resolve s phase))]
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
