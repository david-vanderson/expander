#lang racket/base
(require racket/set
         racket/unit
         "syntax.rkt"
         "scope.rkt"
         "binding.rkt"
         "match.rkt")

(provide core-literal
         core-branch
         
         add-core-form!
         add-core-primitive!

         core-forms
         core-primitives
         
         core-form-sym)

;; Generate an identifier that resolves to the core primitive/form
(define (core-literal sym phase)
  (define id (datum->syntax #f sym))
  (define b (bind sym phase (core-binding sym)))
  (struct-copy syntax id
               [branches (list (branch 'core-literal (list b)))]))

(define (core-branch phase)
  (define b (branch 'core null))
  (for ([sym (in-sequences (in-hash-keys core-primitives)
                           (in-hash-keys core-forms))])
    (set-branch-binds! b (cons (bind sym phase (core-binding sym)) (branch-binds b))))
  b)

;; Core forms are added by `require`s in "main.rkt"

;; Accumulate added core forms and primitives:
(define core-forms (make-hasheq))
(define core-primitives (make-hasheq))

(define (add-core-form! sym proc)
  (hash-set! core-forms sym proc))

(define (add-core-primitive! sym val)
  (hash-set! core-primitives sym val))

;; Helper for recognizing and dispatching on core forms:
(define (core-form-sym s phase)
  (define m (try-match-syntax s '(id . _)))
  (and m
       (let ([b (resolve (m 'id) phase)])
         (and (core-binding? b)
              (core-binding-sym b)))))

