#lang racket/base
(require "syntax.rkt")

(provide resolve
         bound-identifier=?
         free-identifier=?

         (struct-out tip)
         (struct-out bind)
         syntax-tip
         tip-extend!
         tip-pop!
         freeze
         mark
         thaw-introduced)

;; Each syntax object has as pointer (for each phase) to the
;; binding branch tip that represents bindings that affect it.

;; As we expand, we add bindings imperitively to the tip, and
;; any un-expanded syntax using that tip sees the new bindings.

;; As each syntax is expanded, we freeze its tips so it will no
;; longer see new bindings.

;; For each macro invocation, we take introduced syntax and thaw
;; it to a new tip.  This creates the extra dimension of binding
;; that hygiene requires.


;; A branch represents a single binding and points to the
;; previous branch that this binding extends

;; type 'var  -> val is gensym for local variable
;; type 'form -> val is core form
;; type 'prim -> val is core primitive
;; type 'stx  -> val is procedure? for macro, else syntax error

(struct bind (type val)
  #:transparent)

(struct branch (id       ; symbol
                binding  ; bind struct
                prev)    ; #f or branch that this branch extends
  #;#:transparent)


;; A tip holds a branch and is mutable so the branch can be
;; extended at the front
;; it is unique to a given phase
(struct tip (id       ; unique id or 'frozen
             phase    ; integer
             branch)  ; pointer to first branch
  #:transparent #:mutable)


(define (syntax-tip s phase (err? #f))
  (define t (findf (lambda (t) (= phase (tip-phase t))) (syntax-tips s)))
  (when (and err? (not t))
    (error "can't find a tip with phase:" phase s))
  t)


(define (bound-identifier=? a b phase)
  (let ((ta (syntax-tip a phase))
        (tb (syntax-tip b phase)))
    (and (eq? (syntax-e a) (syntax-e b))
         ta tb  ; must have tips
         (eq? ta tb))))


(define (free-identifier=? a b phase)
  (eq? (resolve a phase) (resolve b phase)))


(define (resolve id phase (err? #f))
  (let loop ((b (tip-branch (syntax-tip id phase #t))))
    (cond
      ((not b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f))
      ((equal? (syntax-e id) (branch-id b))  ; found it
       (branch-binding b))
      (else
       (loop (branch-prev b))))))


;; add to this tip's branch
(define (tip-extend! t id bind-type bind-val)
  (set-tip-branch! t (branch id (bind bind-type bind-val) (tip-branch t))))

;; remove most recent binding
(define (tip-pop! t)
  (set-tip-branch! t (branch-prev (tip-branch t))))

;; copy all the tips so this syntax won't be bound be future bindings
(define (freeze s)
  (cond
    [(syntax? s)
     (syntax (freeze (syntax-e s)) (syntax-mark s)
             (map (lambda (t) (tip 'frozen (tip-phase t) (tip-branch t)))
                  (syntax-tips s)))]
    [(list? s) (map freeze s)]
    [else s]))

;; set a mark on all syntax going into a macro
(define (mark s)
  (cond
    [(syntax? s)
     (syntax (mark (syntax-e s)) #t (syntax-tips s))]
    [(list? s) (map mark s)]
    [else s]))

;; thaw all macro-introduced syntax (mark is #f), leave other syntax alone
;; all introduced syntax that was on the same tip when frozen will end
;; up on the same new tip
(define (thaw-introduced s phase)
  (define newtips (make-hasheq))
  (let thaw-introduced* ((s s))
    (cond
      [(and (syntax? s) (not (syntax-mark s)))
       ; introduced syntax, make a new branch
       (define t (syntax-tip s phase #t))
       (unless (equal? 'frozen (tip-id t))
         (error "trying to thaw unfrozen tip" s))
       (define nt (hash-ref newtips (tip-branch t) 'notfound))
       (case nt
         [(notfound)
          (set! nt (tip (gensym 'tip) phase (tip-branch t)))
          ; map old branch to new tip
          (hash-set! newtips (tip-branch t) nt)])

       (when (identifier? s)
         (printf "thaw adding ~a to ~a\n" (tip-id nt) (syntax-e s)))
       (syntax (thaw-introduced* (syntax-e s)) #f (cons nt (remove t (syntax-tips s))))]
      [(and (syntax? s) (syntax-mark s))
       ; not introduced, just reset mark
       (syntax (thaw-introduced* (syntax-e s)) #f (syntax-tips s))]
      [(list? s) (map thaw-introduced* s)]
      [else s])))

