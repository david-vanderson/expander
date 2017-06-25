#lang racket/base
(require racket/set
         "syntax.rkt")

(provide resolve
         bound-identifier=?
         free-identifier=?
         introduce

         (struct-out bind)
         (struct-out branch)
         make-newbranches
         extend-branch
         add-binding!
         mark
         )

;; Each syntax object has a list of branches that hold bindings
;; that affect this syntax.  The first binding in the right phase
;; is what we resolve to.

;; As we expand a binding context, we add a branch to the front of
;; every syntax's branch list in that context.  Then for each
;; identifier being bound, we add a binding to the branch shared
;; by all syntax with that identifier's marks.

;; For each macro invocation, we take introduced syntax and mark
;; it with a unique symbol.  This creates the extra dimension of
;; binding that hygiene requires.

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
(struct bind (phase
              id    ; symbol
              type  ; see above
              [val #:mutable])
  #;#:transparent)


;; syntax s1 could bind s1 if they have the same marks
(define (could-bind? s1 s2)
  (equal? (syntax-marks s1) (syntax-marks s2)))


;; a will bind b if they have the same symbol, marks, and marks-pre
;; binding is reflexive
(define (bound-identifier=? a b phase)
  (and (eq? (syntax-e a) (syntax-e b))
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


(define (introduce s branch)
  (syntax-map s
    (lambda (s)
      ;(when (not (null? (syntax-branches s)))
      ;  (error "already have a branch" s))
      (struct-copy syntax s
                   [branches (cons branch (syntax-branches s))]))))


;; newbranches is a mutable hash that maps mark sets to new branch structs
;; use it to add bindings
(define (make-newbranches)
  (make-hash))

(define (extend-branch s branchid newbranches)
  (syntax-map s
    (lambda (s)
      (cond
        [(and (not (null? (syntax-branches s)))
              (equal? branchid (branch-id (car (syntax-branches s)))))
         ; already have this branch
         ;(when (identifier? s)
         ;    (printf "adding ~a branch ~a oldbranch\n" (syntax-e s) branchid))
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
(define (add-binding! id bind newbranches)
  (define nb (hash-ref newbranches (syntax-marks id) #f))
  (when (not nb)
    (error "add-binding! couldn't find newbranch for" id))
  (set-branch-binds! nb (cons bind (branch-binds nb))))


(define (resolve id phase (err? #f))
  (let loop ((b (syntax-branches id)))
    (cond
      [(null? b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f)]
      [else
       (define bind (findf (lambda (idbind)
                             (and (equal? (syntax-e id) (bind-id idbind))
                                  (equal? phase (bind-phase idbind))))
                           (branch-binds (car b))))
       (if bind
           bind
           (loop (cdr b)))])))

;; ------------------------------------------

;; set a mark m on all syntax going into a macro,
;; or remove mark if we have it already (coming out of a macro)
(define (mark s m)
  (syntax-map s
    (lambda (s)
      (define gotm? (set-member? (syntax-marks s) m))
      (struct-copy syntax s
                   [marks ((if gotm? set-remove set-add) (syntax-marks s) m)]))))
