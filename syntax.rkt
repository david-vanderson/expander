#lang racket/base

(require racket/set)

(provide
 (struct-out syntax) ; includes `syntax?` and `syntax-e`
 identifier?
 bound-identifier=?
 
 syntax->datum
 datum->syntax)

(struct syntax (e      ; datum and nested syntax objects
                marks  ; set of unique ids used to distinguish macro-introduced syntax
                branches) ; list of branches to hold bindings
  #:transparent)

(define empty-marks (seteq))

(define (identifier? s)
  (and (syntax? s) (symbol? (syntax-e s))))

(define (bound-identifier=? a b)
  (and (eq? (syntax-e a) (syntax-e b))
       (equal? (syntax-marks a) (syntax-marks b))))

(define (syntax->datum s)
  (let ([e (syntax-e s)])
    (cond
     [(list? e) (map syntax->datum e)]
     [else e])))

(define (datum->syntax stx-c v)
  (define (wrap e)
    (syntax e
            (if stx-c (syntax-marks stx-c) empty-marks)
            (if stx-c (syntax-branches stx-c) null)))
  (cond
    [(syntax? v) v]
    [(list? v) (wrap (map (lambda (elem-v) (datum->syntax stx-c elem-v))
                          v))]
    [else (wrap v)]))
