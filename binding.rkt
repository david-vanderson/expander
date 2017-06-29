#lang racket/base
(require racket/set
         "syntax.rkt"
         "scope.rkt"
         "namespace.rkt")

(provide
 (struct-out top-level-binding)
 (struct-out local-binding)
 free-identifier=?
 add-local-binding!
 
 empty-env
 env-extend
 
 variable
 (struct-out core-form)
 
 transformer?
 variable?
 
 binding-lookup)

;; ----------------------------------------

;; The only non-local bindings are the core forms and primitives:
(struct top-level-binding (sym))

;; Represent a local binding with a key, where the value of
;; the key is kept in a separate environment. That indirection
;; ensures that a fuly expanded program doesn't reference
;; compile-time values from local bindings, but it records that
;; the binding was local.
(struct local-binding (key))

(define (free-identifier=? a b phase)
  (define ab (resolve a phase))
  (define bb (resolve b phase))
  (cond
   [(top-level-binding? ab)
    (and (top-level-binding? bb)
         (eq? (top-level-binding-sym ab)
              (top-level-binding-sym bb)))]
   [(local-binding? ab)
    (and (local-binding? bb)
         (eq? (local-binding-key ab)
              (local-binding-key bb)))]))

;; Helper for registering a local binding in a set of scopes:
(define (add-local-binding! id)
  (define key (gensym (syntax-e id)))
  (add-binding! id (local-binding key))
  key)

;; ----------------------------------------

;; An expansion environment maps keys to either `variable` or a
;; compile-time value:
(define empty-env #hasheq())
(define (env-extend env key val)
  (hash-set env key val))

;; `variable` is a token to represent a binding to a run-time variable
(define variable (gensym 'variable))
(define (variable? t) (eq? t variable))

;; `missing` is a token to represent the absence of a binding; a
;; distinct token is needed so that it's distinct from all compile-time
;; values
(define missing (gensym 'missing))
(define (missing? t) (eq? t missing))

;; A subset of compile-time values are macro transformers
(define (transformer? t) (procedure? t))

;; A subset of compile-time values are primitive forms
(struct core-form (expander) #:transparent)

;; Returns `variable` or a compile-time value
(define (binding-lookup b env ns id)
  (cond
   [(top-level-binding? b)
    (namespace-get-transformer ns (top-level-binding-sym b) variable)]
   [(local-binding? b)
    (define t (hash-ref env (local-binding-key b) missing))
    (when (eq? t missing)
      (error "identifier used out of context:" id))
    t]
   [else (error "internal error: unknown binding for lookup:" b)]))
