#lang racket/base
(require racket/set
         "syntax.rkt")

(provide resolve
         introduce

         (struct-out branch)
         (struct-out bind)

         make-newbranches
         extend-branch
         add-binding!
         mark)

;; Each syntax object has a list of branches that hold bindings
;; that affect this syntax.  We resolve to the first binding in
;; the branch list with the given phase.

;; As we expand a binding context, we add a branch to the front of
;; all syntax in the binding context.  Syntax with the same marks
;; share the same new branch.  Then for each identifier being bound
;; we add a binding to the shared branch that matches the
;; identifier's marks.  This 2-step process provides the delay needed
;; when binding in a definition context.

;; Each macro invocation adds a unique mark to introduced syntax.
;; This works by marking syntax going into the macro, and then
;; flipping the mark on all syntax coming out.

(struct bind (sym
              phase
              binding)  ; either module-binding? or local-binding?
  #:transparent)

;; branch is mutable for definition contexts
(struct branch (id       ; unique id for this binding context
                [binds #:mutable])  ; list of bindings
  #:transparent)


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
      (struct-copy syntax s
                   [branches (cond
                               [(not branch)
                                null]  ;; used to wipe context
                               [(list? branch)
                                (append branch (syntax-branches s))]
                               [else
                                (cons branch (syntax-branches s))])]))))


;; newbranches is a mutable hash that maps mark sets to new branch structs
;; use it to add bindings:
;; (define newbranches (make-newbranches))
;; (extend-branch <syntax> (gensym) newbranches)
;; (for ((id <ids-to-bind>))
;;   (add-binding! ctx sym <phase> <binding> newbranches))
(define (make-newbranches)
  (make-hash))


;; Add a new branch to all syntax s.  Syntax with the same marks share
;; a copy of the new branch.  Every new branch is recorded in newbranches
;; as a place to add-binding!
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
      

;; Pick the branch in newbranches with the same marks as id
;; and insert the new binding
(define (add-binding! ctx sym phase binding newbranches)
  (define nb (hash-ref newbranches (syntax-marks ctx) #f))
  (when (not nb)
    (error "add-binding! couldn't find newbranch for" ctx))
  (set-branch-binds! nb (cons (bind sym phase binding) (branch-binds nb))))


(define (resolve id phase (err? #f))
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
           (bind-binding bind)
           (loop (cdr b) p))])))

;; ------------------------------------------

;; set a mark m on all syntax going into a macro,
;; or remove mark if we have it already (coming out of a macro)
(define (mark s m)
  (syntax-map s
    (lambda (s)
      (define gotm? (set-member? (syntax-marks s) m))
      (struct-copy syntax s
                   [marks ((if gotm? set-remove set-add) (syntax-marks s) m)]))))
