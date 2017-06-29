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
                marks     ; set of unique ids for macro-introduced syntax
                branches) ; list of branches
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
   [(symbol? v) (syntax v
                        (if ctx (syntax-marks ctx) (seteq))
                        (if ctx (syntax-branches ctx) null))]
   [(list? v) (map (lambda (e) (datum->syntax e ctx)) v)]
   [else v]))

(module+ test
  (check-equal? (datum->syntax 'a)
                (syntax 'a (seteq) (list)))
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

(struct bind (sym phase type val) #:transparent)

;; place to add binds
(struct branch (id [binds #:mutable]) #:transparent)


;; If identifiers are `bound-identifier=?`, they have
;; the same marks so one will bind the other
(define (bound-identifier=? a b)
  (and (eq? (syntax-e a) (syntax-e b))
       (equal? (syntax-marks a) (syntax-marks b))))


(module+ test

  (define loc/a (gensym 'a))
  (define branches/a (list
                      (branch 'let (list (bind 'z 0 'var (gensym 'z))))
                      (branch 'let (list (bind 'a 0 'var loc/a)))))
  ;; Simulates
  ;;   (let ([a 1])
  ;;     (let ([z 2])
  ;;       ....))
  ;; where `a` is bound only once

  (define loc/b-out (gensym 'b))
  (define loc/b-in (gensym 'b))
  (define branches/b (list
                      (branch 'let (list (bind 'b 0 'var loc/b-in)))
                      (branch 'let (list (bind 'b 0 'var loc/b-out)))))
  ;; Simulates
  ;;   (let ([b 1])
  ;;     (let ([b 2])
  ;;       ....))
  ;; where the inner `b` shadows the outer `b`

  (check-equal? (bound-identifier=? (syntax 'a (seteq) branches/a)
                                    (syntax 'a (seteq) branches/a))
                #t)
  (check-equal? (bound-identifier=? (syntax 'a (seteq) branches/a)
                                    (syntax 'z (seteq) branches/a))
                #f)
  
  (define loc/c (gensym 'c))
  (define loc/c-m (lambda (x) x))
  (define loc/c-u (gensym 'c-u))
  (define bind/c-m (bind 'c-m 0 'stx loc/c-m))
  (define stx/c (syntax 'c (seteq)
                        (list
                         (branch 'let (list))
                         (branch 'let (list (bind 'c 0 'var loc/c)))
                         (branch 'let-syntax (list bind/c-m)))))
  (define stx/c-u (syntax 'c (seteq 't1)
                          (list
                           (branch 'let (list (bind 'c 0 'var loc/c-u)))
                           (branch 'let-syntax (list bind/c-m)))))
  ;; Simulates
  ;      (let-syntax ((c-m (lambda (stx)  ; (c-m arg body) -> (let ((c arg)) body)
  ;                          (datum->syntax
  ;                           (quote-syntax here)
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

;; Finds the bind for a given identifier; returns #f if the
;; identifier is unbound
(define (resolve id phase (err? #f))
  ;(printf "resolve ~v\n\n" id)
  (let loop ((b (syntax-branches id)) (p phase))
    (cond
      [(null? b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f)]
      [(branch? (car b))
       (define bind (findf (lambda (bind)
                             (and (eq? (syntax-e id) (bind-sym bind))
                                  (equal? p (bind-phase bind))))
                           (branch-binds (car b))))
       (if bind                
           bind
           (loop (cdr b) p))])))


(module+ test
  (check-equal? (bind-val (resolve (syntax 'a (seteq) branches/a) 0))
                loc/a)
  (check-equal? (resolve (syntax 'a (seteq) branches/b) 0)
                #f)
  (check-equal? (resolve (syntax 'zzz (seteq) branches/a) 0)
                #f)

  (check-equal? (bind-val (resolve (syntax 'b (seteq) branches/b) 0))
                loc/b-in)
  (check-equal? (resolve (syntax 'zzz (seteq) branches/b) 0)
                #f)

  (check-equal? (bind-val (resolve stx/c 0))
                loc/c)
  (check-equal? (bind-val (resolve stx/c-u 0))
                loc/c-u)
  (check-equal? (bind-val (resolve (syntax 'c-m (seteq) (syntax-branches stx/c)) 0))
                loc/c-m)
  (check-equal? (bind-val (resolve (syntax 'c-m (seteq) (syntax-branches stx/c-u)) 0))
                loc/c-m))


(define (syntax-map s f)
  (let loop ((s s))
    (cond
      [(syntax? s)
       (f (struct-copy syntax s [e (loop (syntax-e s))]))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


(define (make-newbranches)
  (make-hash))

(define (extend-branch s branchid newbranches)
  (syntax-map s
    (lambda (s)
      (cond
        [(and (not (null? (syntax-branches s)))
              (ormap (lambda (b)
                       (and (branch? b) (eq? branchid (branch-id b))))
                     (syntax-branches s)))
         ; already have this branch
         ;(when (identifier? s)
         ;  (printf "adding ~a branch ~a oldbranch\n" (syntax-e s) branchid))
         s]
        [else
         (define nb (hash-ref newbranches (syntax-marks s) #f))
         (when (not nb)
           ;(when (identifier? s)
           ;  (printf "adding ~a branch ~a newbranch\n" (syntax-e s) branchid))
           (set! nb (branch branchid '()))
           (hash-set! newbranches (syntax-marks s) nb))
         ;(when (identifier? s)
         ;  (printf "adding ~a branch ~a\n" (syntax-e s) branchid))
         (struct-copy syntax s
                      [branches (cons nb (syntax-branches s))])]))))


  
;; Determine whether two identifiers have the same binding
(define (free-identifier=? a b phase)
  (eq? (resolve a phase) (resolve b phase)))

(module+ test
  (check-equal? (free-identifier=? (syntax 'c-m (seteq) (syntax-branches stx/c))
                                   (syntax 'c-m (seteq) (syntax-branches stx/c-u)) 0)
                #t)
  (check-equal? (free-identifier=? (syntax 'c (seteq) (syntax-branches stx/c))
                                   (syntax 'c (seteq) (syntax-branches stx/c-u)) 0)
                #f))

;; ----------------------------------------
;; Core syntax and primitives

(define core-forms (seteq 'lambda 'let-syntax '#%app 'quote 'quote-syntax))
(define core-primitives (seteq 'datum->syntax 'syntax->datum 'syntax-e
                               'list 'cons 'car 'cdr 'map))

(define (core-branch phase)
  (define b (branch 'core null))
  (for ([sym (in-set core-primitives)])
    (set-branch-binds! b (cons (bind sym phase 'prim sym) (branch-binds b))))
  (for ([sym (in-set core-forms)])
    (set-branch-binds! b (cons (bind sym phase 'form sym) (branch-binds b))))
  b)


;; The `introduce` function adds all the core forms and primitives
;; to the given syntax in the given phase
(define (namespace-syntax-introduce s (phase 0))
  (cond
    ((syntax? s) (syntax (syntax-e s) (syntax-marks s)
                         (cons (core-branch phase) (syntax-branches s))))
    ((list? s) (map (lambda (v) (namespace-syntax-introduce v phase)) s))
    (else s)))


(module+ test
  (check-equal? (resolve (datum->syntax 'lambda stx/c) 0)
                #f)
  (check-equal? (bind-val (resolve (namespace-syntax-introduce (datum->syntax 'lambda)) 0))
                'lambda)) ; i.e., the core `lambda` form


(define (mark s m)
  (syntax-map s
    (lambda (s)
      (define gotm? (set-member? (syntax-marks s) m))
      (struct-copy syntax s
                   [marks ((if gotm? set-remove set-add) (syntax-marks s) m)]))))


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
  (check-equal? (syntax->datum (expand (namespace-syntax-introduce (syntax 'cons (seteq) null))))
                'cons)
  
  ;; A locally-bound variable expands to itself:
  (check-equal? (expand (syntax 'a (seteq) branches/a)) ; bound to `loc1` above
                (syntax 'a (seteq) branches/a))
  
  ;; A free variable triggers an error:
  (check-exn (make-exn:fail? "free variable")
             (lambda ()
               (expand (syntax 'a (seteq) null))))
  
  ;; Application of a locally-bound variable to a number expands to an
  ;; `#%app` form and quotes the number
  (check-equal? (syntax->datum (expand (list (syntax 'a (seteq) branches/a) 1)))
                (list '#%app 'a (list 'quote 1)))
  
  ;; A locally-bound macro expands by applying the macro:
  (check-equal? (syntax->datum
                 (expand (syntax 'a (seteq)
                                 (list (branch 'blah
                                               (list (bind 'a 0 'stx
                                                           (lambda (stx)
                                                             1))))))))
                '(quote 1))
  )


;; Main expander entry point and loop:
(define (expand s (phase 0))
  ;(printf "expand ~v\n\n" (syntax->datum s))
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
         (expand (apply-transformer (bind-val binding) s))
         (error "illegal use of syntax:" s))]
    [else
     s]))

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
        s]
       [else
        (error "missed a core form in expand-id-application-form" (bind-val binding))])]
    [(stx)
     (if (procedure? (bind-val binding))
         (expand (apply-transformer (bind-val binding) s))
         (error "illegal use of syntax:" s))]
    [else
     ;(printf "expand-id-app app ~v\n" s)
     (expand-app s phase)]))

;; Given a macro transformer `t`, apply it --- adding appropriate
;; scopes to represent the expansion step
(define (apply-transformer t s)
  ;; Mark given syntax
  (define m (gensym 't))
  (define marked-s (mark s m))
  ;; Call the transformer
  ;(printf "before t: ~v\n\n" marked-s)
  (define t-s (t marked-s))
  ;(printf "after t: ~v\n\n" t-s)
  (define after-s (mark t-s m))
  ;(printf "after b: ~v\n\n" after-s)
  after-s)

(module+ test
  ;; Check that applying a macro transformer branches the
  ;; introduced parts and leaves original parts alone:
  (let ()
    (define t (lambda (s)
                ;; This transformer converts `(_ f)` to `(f x)`
                (list (list-ref s 1)
                      (datum->syntax 'x (syntax 'zzz (seteq) null)))))

    (define transformed-s
      (apply-transformer t
                         (list (syntax 'm (seteq) null)
                               (syntax 'f (seteq) null))))
  
    (check-equal? (syntax->datum transformed-s)
                  '(f x))
    (check-equal? (set-count (syntax-marks (list-ref transformed-s 0)))
                  0)
    (check-equal? (set-count (syntax-marks (list-ref transformed-s 1)))
                  1)
    )
  )


(define (add-binding! ctx sym phase type val newbranches)
  (define nb (hash-ref newbranches (syntax-marks ctx) #f))
  (when (not nb) 
    (error "add-binding! couldn't find newbranch for" ctx))
  (set-branch-binds! nb (cons (bind sym phase type val) (branch-binds nb))))

;; ----------------------------------------

(define (expand-lambda s phase)
  ;(printf "expand-lambda (~a) ~v\n\n" phase s)
  (match-define `(,lambda-id (,arg-ids ...) ,body) s)

  ;; make new branches to add bindings to
  (define branchid (gensym 'lambda))
  (define newbranches (make-newbranches))
  (set! arg-ids (extend-branch arg-ids branchid newbranches))
  (set! body (extend-branch body branchid newbranches))
  
  (for/list ((id arg-ids))
    (define sym (syntax-e id))
    (add-binding! id sym phase 'var (gensym sym) newbranches))
  
  ;; Expand the function body:
  (define exp-body (expand body phase))

  (list lambda-id arg-ids exp-body))

(define (expand-let-syntax s phase)
  ;(printf "expand-let-syntax ~v\n\n" s)
  (match-define `(,let-syntax-id ([,lhs-ids ,rhss] ...)
                    ,body)
                s)

  ;; make new branches to add bindings to
  (define branchid (gensym 'let-syntax))
  (define newbranches (make-newbranches))
  (set! lhs-ids (extend-branch lhs-ids branchid newbranches))
  (set! body (extend-branch body branchid newbranches))
  
  (for ((lhs-id lhs-ids) (rhs rhss))
    ;; Evaluate compile-time expressions:
    ;(printf "eval-for-syntax\n\n")
    (define rhs-val (eval-for-syntax-binding rhs (add1 phase)))

    ;; add binding
    (define sym (syntax-e lhs-id))
    (add-binding! lhs-id sym phase 'stx rhs-val newbranches))

  ;(printf "expanding body  ~v\n\n" body)
  ;; Expand body
  (define exp-body (expand body phase))

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
