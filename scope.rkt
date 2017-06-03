#lang racket/base
(require "syntax.rkt"
         "expand-context.rkt")

(provide resolve
         bound-identifier=?
         free-identifier=?
         introduce

         (struct-out bind)
         (struct-out branch)
         get-branch
         extend-branch
         add-binding!
         mark
         branch-introduced)

;; Each syntax object has as pointer (for each phase) to the
;; binding branch tip that represents bindings that affect it.

;; As we expand a binding context, we add a branch to the end of
;; every syntax's branch head in that context and phase.  Then for
;; each identifier being bound, we see if that identifier binds
;; each syntax, and if so, we add a bind to that syntax's branch.

;; For each macro invocation, we take introduced syntax and branch
;; it to a new tip with an extra placeholder binding.  This creates
;; the extra dimension of binding that hygiene requires.

;; A branch represents a list of bindings and points to the
;; previous branch that this branch extends

;; branch is mutable for definition contexts
(struct branch (id       ; unique id for this binding context
                [binds #:mutable]  ; list of binds
                prev)    ; #f or branch that this branch extends
  #;#:transparent)

;; type 'var  -> val is gensym for local variable
;; type 'form -> val is core form
;; type 'prim -> val is core primitive
;; type 'stx  -> val is procedure? for macro, else syntax error
;; val is mutable so in letrec-syntaxes we can bind all the ids
;; first and then patch the vals in later
(struct bind (id    ; symbol
              type  ; see above
              [val #:mutable])
  #;#:transparent)


(define (syntax-map s f)
  (let loop ((s s))
    (cond
      [(syntax? s)
       (f (struct-copy syntax s [e (loop (syntax-e s))]))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


(define (introduce s phase branch-head)
  (syntax-map s
    (lambda (s)
      (when (hash-has-key? (syntax-branches s) phase)
        (error "already have a branch head for this phase" phase s))
      (struct-copy syntax s
                   [branches (hash-set (syntax-branches s) phase branch-head)]))))

(define (extend-branch s id phase)
  (syntax-map s
    (lambda (s)
      (define bh (hash-ref (syntax-branches s) phase #f))
      ;(when (identifier? s)
      ;  (printf "~a adding ~a branch ~a\n" phase (syntax-e s) id))
      (struct-copy syntax s
                   [branches (hash-set (syntax-branches s) phase
                                       (branch id '() bh))]))))

(define (get-branch s id phase)
  (let loop ((b (hash-ref (syntax-branches s) phase 'missing)))
    (cond
      [(equal? b 'missing)
       ; this syntax doesn't have a branch in this phase (literals, parenthesis)
       #f]
      [(not b)  ; hit the end
       #f]
      [(equal? id (branch-id b))
       b]  ; found it
      [else
       (loop (branch-prev b))])))

(define (branches-equal? a b)
  (cond
    [(and (not a) (not b))
     #t]
    [(and a b (equal? (branch-id a) (branch-id b)))
     (branches-equal? (branch-prev a) (branch-prev b))]
    [else
     #f]))
      

;; For all syntax s, if it has a branch with branchid-prefix somewhere,
;; then we are binding it, which means add bind to the list of binds
;; in the branch branchid-to-bind
(define (add-binding! s phase branch-prefix branchid-to-bind bind)
  (let loop ((s s))
    ;(printf "  add-binding ~v\n" s)
    (cond
      [(syntax? s)
       (define b (get-branch s (branch-id branch-prefix) phase))
       (when (branches-equal? branch-prefix b)
         ;(when (identifier? s)
         ;  (printf "~a add-binding! ~a bind ~a prefix ~a in ~a\n"
         ;          phase (syntax-e s) (bind-id bind) (branch-id branch-prefix) branchid-to-bind))
         
         (define b (get-branch s branchid-to-bind phase))
         (set-branch-binds! b (cons bind (branch-binds b))))
       (loop (syntax-e s))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


;; I'm not sure bound-identifier=? can always be reflective
;; This implementation will work for syntax that hasn't been expanded before
;; but for already-expanded syntax we need something else
(define (bound-identifier=? a b phase)
  ; do these live on the same tip, so that binding one will affect the other?
  (and (eq? (syntax-e a) (syntax-e b))
       (let ((ba (hash-ref (syntax-branches a) phase #f))
             (bb (hash-ref (syntax-branches b) phase #f)))
         (and ba bb  ; must have branches
              (eq? ba bb)))))


(define (free-identifier=? a b phase)
  ; do these resolve to the same binding?
  ; possibly through different branches that join as you go back
  (eq? (resolve a phase) (resolve b phase)))


(define (resolve id phase (err? #f))
  (let loop ((b (hash-ref (syntax-branches id) phase)))
    (cond
      [(not b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f)]
      [else
       (define bind (findf (lambda (idbind) (equal? (syntax-e id) (bind-id idbind)))
                           (branch-binds b)))
       (if bind
           bind
           (loop (branch-prev b)))])))

;; ------------------------------------------

;; set a mark m on all syntax going into a macro
(define (mark s m)
  (syntax-map s
    (lambda (s)
      (struct-copy syntax s
                   [marks (cons m (syntax-marks s))]))))

;; branch all macro-introduced syntax (top mark is not m)
(define (branch-introduced s m branchid)
  (syntax-map s
    (lambda (s)
      (define intro? (or (null? (syntax-marks s))
                         (not (equal? m (car (syntax-marks s))))))
      (struct-copy syntax s
                   [marks (if intro?
                              (syntax-marks s)
                              (cdr (syntax-marks s)))]
                   [branches
                    (cond
                      [(not intro?) (syntax-branches s)]
                      [else
                       (for/hash ([(p b) (in-hash (syntax-branches s))])
                         ;(when (identifier? s)
                         ;  (printf "~a branch ~a from ~a to ~a\n" p (syntax-e s) (branch-id b) branchid))
                         (values p (branch branchid '() b)))])]))))
