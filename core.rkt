#lang racket/base
(require racket/set
         racket/unit
         "syntax.rkt"
         "scope.rkt"
         "binding.rkt"
         "match.rkt"
         "namespace.rkt")

(provide add-core-form!
         add-core-primitive!
         
         declare-core-module!
         
         core-form-sym)

;; Core forms and primitives are added by `require`s in "main.rkt"

;; Accumulate added core forms and primitives:
(define core-forms #hasheq())
(define core-primitives #hasheq())

(define (add-core-form! sym proc)
  (set! core-forms (hash-set core-forms
                             sym
                             proc)))

(define (add-core-primitive! sym val)
  (set! core-primitives (hash-set core-primitives
                                  sym
                                  val)))

;; Used only after filling in all core forms and primitives:
(define (declare-core-module! ns)
  (declare-module!
   ns
   '#%core
   (make-module '#%core
                #hasheq()
                (hasheqv 0 (for/hasheq ([sym (in-sequences
                                              (in-hash-keys core-primitives)
                                              (in-hash-keys core-forms))])
                             (values sym (module-binding '#%core 0 sym
                                                         '#%core 0 sym
                                                         0))))
                0 1
                (lambda (ns phase phase-level)
                  (case phase-level
                    [(0)
                     (for ([(sym val) (in-hash core-primitives)])
                       (namespace-set-variable! ns 0 sym val))]
                    [(1)
                     (for ([(sym proc) (in-hash core-forms)])
                       (namespace-set-transformer! ns 0 sym (core-form proc)))])))))

;; Helper for recognizing and dispatching on core forms:
(define (core-form-sym s phase)
  (define m (try-match-syntax s '(id . _)))
  (and m
       (let ([b (resolve (m 'id) phase)])
         (and (module-binding? b)
              (eq? '#%core (module-binding-module b))
              (module-binding-sym b)))))
