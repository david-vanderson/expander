#lang racket/base
(require racket/set
         racket/unit
         "syntax.rkt"
         "scope.rkt"
         "binding.rkt"
         "match.rkt"
         "namespace.rkt")

(provide core-literal
         core-branch
         
         add-core-form!
         add-core-primitive!
         
         declare-core-top-level!
         
         core-form-sym)

;; Generate an identifier that resolves to the core primitive/form
(define (core-literal sym phase)
  (define id (datum->syntax #f sym))
  (define b (bind sym phase (top-level-binding sym)))
  (struct-copy syntax id
               [branches (list (branch 'core-literal (list b)))]))

(define (core-branch phase)
  (define b (branch 'core null))
  (for ([sym (in-sequences (in-hash-keys core-primitives)
                           (in-hash-keys core-forms))])
    (set-branch-binds! b (cons (bind sym phase (top-level-binding sym)) (branch-binds b))))
  b)

;; Core forms are added by `require`s in "main.rkt"

;; Accumulate added core forms and primitives:
(define core-forms (make-hasheq))
(define core-primitives (make-hasheq))

(define (add-core-form! sym proc)
  (hash-set! core-forms sym proc))

(define (add-core-primitive! sym val)
  (hash-set! core-primitives sym val))

;; Used only after filling in all core forms and primitives:
(define (declare-core-top-level! ns)
  (for ([(sym val) (in-hash core-primitives)])
    (namespace-set-variable! ns sym val))
  (for ([(sym proc) (in-hash core-forms)])
    (namespace-set-transformer! ns sym (core-form proc))))

;; Helper for recognizing and dispatching on core forms:
(define (core-form-sym s phase)
  (define m (try-match-syntax s '(id . _)))
  (and m
       (let ([b (resolve (m 'id) phase)])
         (and (top-level-binding? b)
              (top-level-binding-sym b)))))

