#lang racket/base
(require "syntax.rkt")

(provide resolve
         bound-identifier=?
         introduce

         extend-branch
         add-binding!
         mark-pre
         mark-post
         )

;; Each syntax object has a branch list for each phase that
;; contains all the bindings that affect it.  Resolve an identifier
;; by finding the first bind in the list with the same symbol.

;; As we expand a binding context, we add a branch to the start of
;; every syntax's branch list in that context and phase.  Then for
;; each identifier being bound, we see if that identifier could-bind?
;; each syntax, and if so, we add the new bind to that syntax's branch.

;; For each macro invocation, we take introduced syntax and add a unique
;; mark.  could-bind? only works for syntax with equal marks.  This creates
;; the extra dimension of binding that hygiene requires.

(struct bind (sym        
              binding)  ; either module-binding? or local-binding?
  #:transparent)

;; branch is mutable for definition contexts
(struct branch (id       ; unique id for this binding context
                [binds #:mutable])  ; list of bindings
  #:transparent)


;; syntax s1 could bind s1 if they have the same marks and marks-pre
(define (could-bind? s1 s2)
  (and (equal? (syntax-marks s1) (syntax-marks s2))
       (equal? (syntax-marks-pre s1) (syntax-marks-pre s2))))


;; a will bind b if they have the same symbol, marks, and marks-pre
;; binding is reflexive
(define (bound-identifier=? a b phase)
  (and (equal? (syntax-e a) (syntax-e b))
       (could-bind? a b)))


(define (syntax-map s f)
  (let loop ((s s))
    (cond
      [(syntax? s)
       (f (struct-copy syntax s [e (loop (syntax-e s))]))]
      [(list? s) (map loop s)]
      [(pair? s) (cons (loop (car s))
                       (loop (cdr s)))]
      [else s])))


(define (introduce s new-branches new-prephase-branchids [err-if-exists? #t])
  (syntax-map s
    (lambda (s)
      (when (and err-if-exists? (not (hash-empty? (syntax-branches s))))
        (error "already have branches" s))
      (struct-copy syntax s
                   [branches (hash-copy new-branches)]
                   [prephase-branchids (map values new-prephase-branchids)]))))


(define (extend-branch s branchid phase)
  ;(printf "extend-branch ~a ~a on ~v\n\n" phase branchid s)
  (syntax-map s
    (lambda (s)
      (cond
        [(equal? 'all phase)
         ; on module require, we need a new branch for all phases
         ; but not all phases are realized
         (define newbranches (make-hash))
         (for ([(p b) (in-hash (syntax-branches s))])
           (hash-set! newbranches p (cons (branch branchid null) b)))
         (struct-copy syntax s
                   [branches newbranches]
                   [prephase-branchids (cons branchid (syntax-prephase-branchids s))])]
        [else
         (define bh (hash-ref (syntax-branches s) phase #f))
         (when (not bh)
           (set! bh (map (lambda (id) (branch id null)) (syntax-prephase-branchids s))))
         (define newbranches (hash-copy (syntax-branches s)))
         (hash-set! newbranches phase (cons (branch branchid '()) bh))
         ;(when (identifier? s)
         ;  (printf "~a adding ~a branch ~a\n" phase (syntax-e s) id))
         (struct-copy syntax s
                      [branches newbranches])]))))
      

;; For all syntax s, if (could-bind? id s)
;; then we are binding it, which means add a bind to the list of binds
;; in the branch identified by branchid
(define (add-binding! s id binding branchid phase)
  ;(printf "add-binding! id ~v binding ~v to ~v\n\n" (syntax-marks id) binding s)
  (let loop ((s s))
    ;(printf "  add-binding ~v\n" s)
    (cond
      [(syntax? s)
       ;(printf "  add-binding syntax ~v\n" s)
       ;(printf "  add-binding syntax marks ~v\n" (syntax-marks s))
       (when (could-bind? id s)
         (define b
           (let loop ((br (hash-ref (syntax-branches s) phase #f)))
             (cond
               [(not br)
                ; this syntax doesn't have a branch in this phase (literals, parenthesis)
                ; try realizing this phase first
                (define bh (map (lambda (id) (branch id null)) (syntax-prephase-branchids s)))
                (hash-set! (syntax-branches s) phase bh)
                (loop bh)]
               [(null? br)  ; hit the end
                ;(printf "couldn't find branch ~a in phase ~a for ~v\n\n" branchid phase s)
                #f]
               [(equal? branchid (branch-id (car br)))
                (car br)]  ; found it
               [else
                (loop (cdr br))])))
         (when b
           #;(when (identifier? s)
             (printf "~a add-binding! ~a bind ~a in ~a\n"
                     phase (syntax-e s) (syntax-e id) branchid))
           (set-branch-binds! b (cons (bind (syntax-e id) binding) (branch-binds b)))))
       (loop (syntax-e s))]
      [(list? s) (for-each loop s)]
      [(pair? s) (begin (loop (car s))
                        (loop (cdr s)))]
      [else s])))


(define (resolve id phase (err? #t))
  (let loop ((b (if err?
                    (hash-ref (syntax-branches id) phase
                              (lambda () (error 'resolve "no branch for phase ~a in ~v" phase id)))
                    (hash-ref (syntax-branches id) phase null))))
    (cond
      [(null? b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f)]
      [else
       (define bind (findf (lambda (bind) (equal? (syntax-e id) (bind-sym bind)))
                           (branch-binds (car b))))
       (if bind
           (bind-binding bind)
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
