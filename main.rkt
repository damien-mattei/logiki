#lang racket/base

;; λογικι (logiki) : symbolic computation of propositional logic , written in Scheme+
;;
;; (require logiki) gives the procedures of logiki+.rkt (normal forms , minimal forms , logic-test ...) and the
;; conversions between prefix and infix notations of operation+.rkt (prefix->infix-symb , n-arity ...)

(require "logiki+.rkt"
	 "operation+.rkt")

(provide (all-from-out "logiki+.rkt")
	 (all-from-out "operation+.rkt"))
