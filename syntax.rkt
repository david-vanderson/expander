#lang racket/base

(require racket/set)

(provide
 (struct-out syntax) ; includes `syntax?` and `syntax-e`
 identifier?

 empty-branches
 
 syntax->datum
 datum->syntax
 
 syntax-property)

(struct syntax (e      ; datum and nested syntax objects
                marks  ; set of unique ids used to distinguish macro-introduced syntax
                branches  ; list of branches
                srcloc ; source location
                props) ; properties
        ;; Custom printer:
        #:property prop:custom-write
        (lambda (s port mode)
          (write-string "#<syntax:" port)
          (fprintf port "~.s" (syntax->datum s))
          (write-string ">" port))
  #:transparent)

(define empty-marks (seteq))
(define empty-branches null)
(define empty-props #hash())

(define (identifier? s)
  (and (syntax? s) (symbol? (syntax-e s))))

(define (syntax->datum s)
  (let loop ([s/e (syntax-e s)])
    (cond
     [(syntax? s/e) (loop (syntax-e s/e))]
     [(pair? s/e) (cons (loop (car s/e))
                        (loop (cdr s/e)))]
     [else s/e])))

(define (datum->syntax stx-c v [stx-l #f] [stx-p #f])
  (define (wrap e)
    (syntax e
            (if stx-c (syntax-marks stx-c) empty-marks)
            (if stx-c (syntax-branches stx-c) empty-branches)
            (and stx-l (syntax-srcloc stx-l))
            (if stx-p (syntax-props stx-p) empty-props)))
  (cond
   [(syntax? v) v]
   [(list? v) (wrap (for/list ([elem-v (in-list v)])
                      (datum->syntax stx-c elem-v stx-l stx-p)))]
   [(pair? v) (wrap (cons (datum->syntax stx-c (car v) stx-l stx-p)
                          (datum->syntax stx-c (cdr v) stx-l stx-p)))]
   [else (wrap v)]))

(define syntax-property
  (case-lambda
    [(s key)
     (unless (syntax? s)
       (raise-argument-error 'syntax-property "syntax" s))
     (hash-ref (syntax-props s) key #f)]
    [(s key val)
     (unless (syntax? s)
       (raise-argument-error 'syntax-property "syntax" s))
     (struct-copy syntax s
                  [props (hash-set (syntax-props s) key val)])]))
