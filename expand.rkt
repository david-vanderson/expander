#lang racket/base
(require "syntax.rkt"
         "scope.rkt"
         "match.rkt")

(provide expand)

;; ----------------------------------------

;; Main expander loop:
(define (expand s phase)
  (cond
   [(identifier? s)
    (expand-identifier s phase)]
   [(and (pair? (syntax-e s))
         (identifier? (car (syntax-e s))))
    (expand-id-application-form s phase)]
   [(or (pair? (syntax-e s))
        (null? (syntax-e s)))
    ;; An "application" form that doesn't start with an identifier
    (expand-app s phase)]
   [else
    ;; Anything other than an identifier or parens is implicitly quoted
    (freeze (datum->syntax s (list (datum->syntax s 'quote) s)))]))

;; An identifier by itself:
(define (expand-identifier s phase)
  (define binding (resolve s phase #t))
  (case (bind-type binding)
    [(form)
     ((bind-val binding) s phase)]
    [(stx)
     (if (procedure? (bind-val binding))
         (expand (apply-transformer (bind-val binding) s phase) phase)
         (error "illegal use of syntax:" s))]
    [(prim var)
     (freeze s)]
    [else
     (error "missed bind-type case:" (bind-type binding))]))

;; An "application" form that starts with an identifier
(define (expand-id-application-form s phase)
  (define id (car (syntax-e s)))
  (define binding (resolve id phase))
  (cond
    [(or (not binding)
         (equal? 'var (bind-type binding))
         (equal? 'prim (bind-type binding)))
     (expand-app s phase)]
    [(equal? 'form (bind-type binding))
     ((bind-val binding) s phase)]
    [(equal? 'stx (bind-type binding))
     (if (procedure? (bind-val binding))
         (expand (apply-transformer (bind-val binding) s phase) phase)
         (error "illegal use of syntax:" s))]
    [else
     (error "missed bind-type case:" (bind-type binding))]))


;; Apply macro transformer
(define (apply-transformer t s phase)
  ;; Mark given syntax
  (define marked-s (mark s))
  ;; Call the transformer
  ;(printf "before t: ~v\n\n" marked-s)
  (define t-s (t marked-s))
  (unless (syntax? t-s)
    (error "transformer produced non-syntax:" t-s))
  ;(printf "after t: ~v\n\n" t-s)
  (define after-s (thaw-introduced t-s phase))
  ;(printf "after b: ~v\n\n" after-s)
  after-s)

;; ----------------------------------------

;; Expand an application (i.e., a function call)
;; All we do is insert a '#%app and recur
;; expanding the other stuff is left for the '#%app core form
(define (expand-app s phase)
  (define m (match-syntax s '(rator rand ...)))
  (expand
   (datum->syntax s
                  (list* (datum->syntax s '#%app)
                         (m 'rator)
                         (m 'rand)))
   phase))

