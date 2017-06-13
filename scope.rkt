#lang racket/base
(require "syntax.rkt")

(provide resolve
         bound-identifier=?
         free-identifier=?
         introduce

         (struct-out bind)
         (struct-out branch)
         extend-branch
         add-binding!
         mark-pre
         mark-post
         )

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
                [binds #:mutable])  ; list of binds
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


;; syntax s1 could bind s1 if they have the same marks and marks-pre
(define (could-bind? s1 s2)
  (and (equal? (syntax-marks s1) (syntax-marks s2))
       (equal? (syntax-marks-pre s1) (syntax-marks-pre s2))))


;; a will bind b if they have the same symbol, marks, and marks-pre
;; binding is reflexive
(define (bound-identifier=? a b phase)
  (and (equal? (syntax-e a) (syntax-e b))
       (could-bind? a b)))


(define (free-identifier=? a b phase)
  ; do these resolve to the same binding?
  (eq? (resolve a phase) (resolve b phase)))


(define (syntax-map s f)
  (let loop ((s s))
    (cond
      [(syntax? s)
       (f (struct-copy syntax s [e (loop (syntax-e s))]))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


(define (introduce s phase branch)
  (syntax-map s
    (lambda (s)
      (when (hash-has-key? (syntax-branches s) phase)
        (error "already have a branch head for this phase" phase s))
      (struct-copy syntax s
                   [branches (hash-set (syntax-branches s) phase (list branch))]))))

(define (extend-branch s id phase)
  (syntax-map s
    (lambda (s)
      (define bh (hash-ref (syntax-branches s) phase #f))
      ;(when (identifier? s)
      ;  (printf "~a adding ~a branch ~a\n" phase (syntax-e s) id))
      (struct-copy syntax s
                   [branches (hash-set (syntax-branches s) phase
                                       (cons (branch id '()) bh))]))))


(define (get-branch s phase id)
  (let loop ((b (hash-ref (syntax-branches s) phase 'missing)))
    (cond
      [(equal? b 'missing)
       ; this syntax doesn't have a branch in this phase (literals, parenthesis)
       #f]
      [(null? b)  ; hit the end
       #f]
      [(equal? id (branch-id (car b)))
       (car b)]  ; found it
      [else
       (loop (cdr b))])))
      

;; For all syntax s, if (could-bind? id s)
;; then we are binding it, which means add bind to the list of binds
;; in the branch identified by branchid
(define (add-binding! s id bind branchid phase)
  (let loop ((s s))
    ;(printf "  add-binding ~v\n" s)
    (cond
      [(syntax? s)
       (when (could-bind? id s)
         (define b (get-branch s phase branchid))
         (when b
           ;(when (identifier? s)
           ;  (printf "~a add-binding! ~a bind ~a in ~a\n"
           ;          phase (syntax-e s) (bind-id bind) branchid))
           (set-branch-binds! b (cons bind (branch-binds b)))))
       (loop (syntax-e s))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


(define (resolve id phase (err? #f))
  (let loop ((b (hash-ref (syntax-branches id) phase)))
    (cond
      [(null? b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f)]
      [else
       (define bind (findf (lambda (idbind) (equal? (syntax-e id) (bind-id idbind)))
                           (branch-binds (car b))))
       (if bind
           bind
           (loop (cdr b)))])))

;; ------------------------------------------

;; set a mark m on all syntax going into a macro
(define (mark-pre s m)
  (syntax-map s
    (lambda (s)
      (struct-copy syntax s
                   [marks-pre (cons m (syntax-marks-pre s))]))))

;; for syntax coming out of a macro
;; if marks-pre has m, remove it (syntax was argument to macro)
;; if not, add it to marks (syntax was introduced)
(define (mark-post s m)
  (syntax-map s
    (lambda (s)
      (define gotm? (and (not (null? (syntax-marks-pre s)))
                         (equal? m (car (syntax-marks-pre s)))))
      (struct-copy syntax s
                   [marks-pre (if gotm?
                                  (cdr (syntax-marks-pre s))
                                  (syntax-marks-pre s))]
                   [marks (if gotm?
                              (syntax-marks s)
                              (cons m (syntax-marks s)))]))))
