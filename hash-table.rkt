#lang reader SRFI-105

;; logiki : hash tables (hash-table-clear!)

(module hash-table racket

(provide (all-defined-out))

(require srfi/69)

;; from hash-table.scm of library-FunctProg (the file is kept there for the other Scheme implementations)


;; delete all the elements of a hash table but not the hash table itself (will be done by garbage collector)

(define (hash-table-clear! ht) (map (lambda (key) (hash-table-delete! ht key))
				    (hash-table-keys ht)))


) ; end module
