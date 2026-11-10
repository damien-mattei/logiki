#lang reader SRFI-105

;; logiki : symbolic numbers (zero-symb? , unity-symb? ...)

(module symbolic racket

(provide (all-defined-out))


;; from symbolic.scm of library-FunctProg (the file is kept there for the other Scheme implementations)

(define (zero-symb? x)
  (and (number? x) (zero? x)))

(define (unity-symb? x)
  (and (number? x) (=  1 x)))


(define (symbolic-1 expr)
  (if (number? expr)
      (- expr 1)
      expr))


) ; end module
