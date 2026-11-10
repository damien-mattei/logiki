#lang info
(define collection "logiki")
(define pkg-desc "λογικι (logiki) : symbolic computation of propositional logic in Scheme+ , disjunctive and conjunctive normal forms , minimal forms by the Quine-McCluskey and Petrick methods")
(define version "21.1")
(define pkg-authors '(mattei))
(define license 'GPL-3.0-or-later)
(define deps '("base"
	       "srfi-lib"
	       "r6rs-lib"
	       "version-case"
	       "Scheme-PLUS-for-Racket"
	       "SRFI-105-for-Racket"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/logiki.scrbl" ())))
