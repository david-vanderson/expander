#lang racket

(provide
 (struct-out syntax) ; includes `syntax?` and `syntax-e`
 identifier?
 
 syntax->datum
 datum->syntax)

(struct syntax (e      ; datum and nested syntax objects
                mark   ; #t or #f to distinguish introduced syntax
                tips)  ; list of tips, one for each phase
  #:transparent)

(define (identifier? s)
  (and (syntax? s) (symbol? (syntax-e s))))

(define (syntax->datum s)
  (let ([e (syntax-e s)])
    (cond
     [(list? e) (map syntax->datum e)]
     [else e])))

(define (datum->syntax stx-c v)
  (define (wrap e)
    (syntax e #f (if stx-c
                     (syntax-tips stx-c)
                     (list))))
  (cond
   [(syntax? v) v]
   [(list? v) (wrap (map (lambda (elem-v) (datum->syntax stx-c elem-v))
                         v))]
   [else (wrap v)]))
