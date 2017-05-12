#lang racket/base
(require "syntax.rkt")

(provide resolve
         bound-identifier=?
         free-identifier=?
         introduce

         (struct-out tip)
         (struct-out bind)
         syntax-tip
         tip-extend!
         tip-pop!
         freeze
         mark
         thaw-introduced
         snip-tips!)

;; Each syntax object has as pointer (for each phase) to the
;; binding branch tip that represents bindings that affect it.

;; As we expand, we add/remove bindings imperitively to the tip
;; so un-expanded syntax using that tip sees the new bindings.

;; As each syntax is expanded, we freeze its tips so it will
;; remember the exact bindings in effect as it was expanded.

;; For each macro invocation, we take introduced syntax and thaw
;; it to a new tip.  This creates the extra dimension of binding
;; that hygiene requires.


;; A branch represents a single binding and points to the
;; previous branch that this binding extends

;; type 'var  -> val is gensym for local variable
;; type 'form -> val is core form
;; type 'prim -> val is core primitive
;; type 'stx  -> val is procedure? for macro, else syntax error
;; bind is mutable so in letrec-syntaxes we can bind all the ids
;; first and then patch the vals in later
(struct bind (type val)
  #:transparent #:mutable)

;; branch is mutable for definition contexts, where it can point to
;; tips that we later need to snip out
(struct branch (id       ; symbol
                binding  ; bind struct
                prev)    ; #f or branch that this branch extends (or tip in definition context)
  #:transparent #:mutable)


;; A tip holds a branch and is mutable so the branch can be
;; extended at the front
;; it is unique to a given phase
(struct tip (id       ; unique id or 'frozen
             phase    ; integer
             branch)  ; pointer to first branch or another tip in a definition context
  #:transparent #:mutable)


(define (syntax-tip s phase (err? #f))
  (define t (findf (lambda (t) (= phase (tip-phase t))) (syntax-tips s)))
  (when (and err? (not t))
    (error "can't find a tip with phase:" phase s))
  t)


(define (introduce s phase tip)
  (define (nsi s) (introduce s phase tip))
  (cond
    [(syntax? s)
     (when (syntax-tip s phase)
       (error "already have a tip for this phase" phase s))
     (struct-copy syntax s
                  [e (nsi (syntax-e s))]
                  [tips (cons tip (syntax-tips s))])]
    [(list? s) (map nsi s)]
    [(pair? s) (cons (nsi (car s))
                     (nsi (cdr s)))]
    [else s]))


(define (bound-identifier=? a b phase)
  ; do these live on the same tip, so that binding one will affect the other?
  (and (eq? (syntax-e a) (syntax-e b))
       (let ((ta (syntax-tip a phase))
             (tb (syntax-tip b phase)))
         (and ta tb  ; must have tips
              (eq? ta tb)))))


(define (free-identifier=? a b phase)
  ; do these resolve to the same binding?
  ; possibly through different branches that join as you go back
  (eq? (resolve a phase) (resolve b phase)))


(define (resolve id phase (err? #f))
  (let loop ((b (tip-branch (syntax-tip id phase #t))))
    (cond
      ((not b)  ; ran out of branches
       (if err?
           (error "unbound identifier in phase:" phase id)
           #f))
      ((tip? b)
       ;; only in definition contexts
       (loop (tip-branch b)))
      ((equal? (syntax-e id) (branch-id b))  ; found it
       (branch-binding b))
      (else
       (loop (branch-prev b))))))


(define (snip-tips! tip)
  (when (tip? (tip-branch tip))
    (set-tip-branch! tip (tip-branch (tip-branch tip)))
    (snip-tips! tip))
  (let loop ((b (tip-branch tip)))
    (cond
      [(not b)  ; done
       (void)]
      [(tip? (branch-prev b))
       ;; only in definition contexts
       (set-branch-prev! b (tip-branch (branch-prev b)))]
      [else
       (loop (branch-prev b))])))


;; add to this tip's branch
(define (tip-extend! t id bind-type bind-val)
  (set-tip-branch! t (branch id (bind bind-type bind-val) (tip-branch t))))

;; remove most recent binding
(define (tip-pop! t)
  (set-tip-branch! t (branch-prev (tip-branch t))))

;; copy all the tips so this syntax won't be bound be future bindings
(define (freeze s [record-tips #f])
  (cond
    [(syntax? s)
     (struct-copy syntax s
                  [e (freeze (syntax-e s))]
                  [tips (map (lambda (t)
                               (if record-tips
                                   (let ()
                                     ;; definition context, point it to the previous tip
                                     (define newt
                                       (struct-copy tip t [id 'frozen] [branch t]))
                                     (set-box! record-tips (cons newt (unbox record-tips)))
                                     newt)
                                   (struct-copy tip t [id 'frozen])))
                             (syntax-tips s))])]
    [(list? s) (map freeze s)]
    [(pair? s) (cons (freeze (car s))
                     (freeze (cdr s)))]
    [else s]))


;; ------------------------------------------

;; set a mark on all syntax going into a macro
(define (mark s)
  (cond
    [(syntax? s)
     (struct-copy syntax s
                  [e (mark (syntax-e s))]
                  [mark #t])]
    [(list? s) (map mark s)]
    [(pair? s) (cons (mark (car s))
                     (mark (cdr s)))]
    [else s]))

;; thaw all macro-introduced syntax (mark is #f), leave other syntax alone
;; all introduced syntax that was on the same tip when frozen will end
;; up on the same new tip
(define (thaw-introduced s phase [record-tips #f])
  (define newtips (make-hasheq))
  (let thaw-introduced* ((s s))
    (cond
      [(and (syntax? s) (not (syntax-mark s)))
       ; introduced syntax, make a new branch
       (define t (syntax-tip s phase))
       (cond
         [(not t)
          (when (identifier? s)
            (error "can't find a tip with phase for identifier:" phase s))
          ; a lot of macros do (datum->syntax #f (list ...))
          ; where they don't care about the binding environment of the parenthesis
          ; so we will ignore that special case
          (struct-copy syntax s
                       [e (thaw-introduced* (syntax-e s))]
                       [mark #f])]
         [else
          (unless (equal? 'frozen (tip-id t))
            (error "trying to thaw unfrozen tip" s))
          (define nt (hash-ref newtips (tip-branch t) 'notfound))
          (when (equal? 'notfound nt)
            (set! nt (tip (gensym 'tip) phase (tip-branch t)))
            ; map old branch to new tip
            (hash-set! newtips (tip-branch t) nt)
            (when record-tips
              (set-box! record-tips (cons nt (unbox record-tips)))))
          
          (when (identifier? s)
            (printf "thaw adding ~a to ~a\n" (tip-id nt) (syntax-e s)))
          (struct-copy syntax s
                       [e (thaw-introduced* (syntax-e s))]
                       [mark #f]
                       [tips (cons nt (remove t (syntax-tips s)))])])]
      [(and (syntax? s) (syntax-mark s))
       ; not introduced, just reset mark
       (struct-copy syntax s
                    [e (thaw-introduced* (syntax-e s))]
                    [mark #f])]
      [(list? s) (map thaw-introduced* s)]
      [(pair? s) (cons (thaw-introduced* (car s))
                       (thaw-introduced* (cdr s)))]
      [else s])))
