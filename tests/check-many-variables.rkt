#lang reader SRFI-105

;; raco test : the two ways to find the minterms of a formula (see by-distribution? in logiki+.rkt). The distribution
;; explodes with the structure of the formula , the truth table with the number of variables (2^n lines) : the
;; minimal forms must stay fast for a formula of 20 variables close to a normal form , and for a formula of 4
;; variables whose normal form by distribution is big. The test fails if a result is wrong or takes more than 20 s.

(module check-many-variables racket

(require Scheme+)
(require logiki)

{failures <- 0}

;; the result of the thunk , or 'too-slow after 20 s
(define (in-time thunk)
  {result <- 'too-slow}
  {th <- (thread (λ () {result <- (thunk)}))}
  (unless (sync/timeout 20 th)
    (kill-thread th))
  result)

(define (report label ok)
  (display label) (display " : ") (display (if ok "ok" "******* WRONG OR TOO SLOW *******")) (newline)
  (unless ok {failures <- failures + 1}))

(define (variables n)
  (build-list n (λ (i) (string->symbol (format "x~a" i)))))

;; the same value for the two formulas on k assignments at random
(define (same-on-random-assignments? e1 e2 var-list k)
  (andmap (λ (i)
	    {env <- (map (λ (v) (cons v {(random 2) = 0})) var-list)}
	    (eq? (formula-value e1 env) (formula-value e2 env)))
	  (range k)))

;; the same operator and the same arguments , in any order
(define (same-operation? r e)
  (and (pair? r)
       (eq? (car r) (car e))
       {(length (cdr r)) = (length (cdr e))}
       (andmap (λ (x) (memq x (cdr r))) (cdr e))))

(random-seed 7)
{vs <- (variables 20)}

;; a disjunction of 20 variables : already minimal , but 2^20 - 1 minterms
{big-or <- (cons 'or vs)}
(report "minimal-dnf of a disjunction of 20 variables"
	(same-operation? (in-time (λ () (minimal-dnf big-or))) big-or))

;; a conjunction of 20 variables : one minterm , 2^20 - 1 maxterms
{big-and <- (cons 'and vs)}
(report "minimal-dnf of a conjunction of 20 variables"
	(same-operation? (in-time (λ () (minimal-dnf big-and))) big-and))

;; a function of 20 variables given by 40 minterms
{minterms <- (build-list 40 (λ (i) (cons 'and (map (λ (v) (if {(random 2) = 0} v (list 'not v))) vs))))}
{sparse <- (cons 'or minterms)}
{r <- (in-time (λ () (minimal-dnf sparse)))}
(report "minimal-dnf of 40 minterms of 20 variables"
	(and (not (eq? r 'too-slow))
	     (same-on-random-assignments? r sparse vs 5000)
	     ;; true on each minterm
	     (andmap (λ (mt)
		       (formula-value r (map (λ (v l) (cons v (symbol? l))) vs (cdr mt))))
		     minterms)))
(report "minterm-numbers of 40 minterms of 20 variables"
	(let ((ns (in-time (λ () (minterm-numbers sparse)))))
	  (and (list? ns) {(length ns) = (length (remove-duplicates minterms))})))

;; formulas of 4 variables whose disjunctive normal form by distribution is big
(for-each (λ (e)
	    {sizes <- (distribution-sizes (normalize-formula e))}
	    (report (format "minimal-dnf and minimal-cnf of ~a (~a terms by distribution)" e (car sizes))
		    (let ((d (in-time (λ () (minimal-dnf e))))
			  (c (in-time (λ () (minimal-cnf e)))))
		      (and {(car sizes) > 64}
			   (not (eq? d 'too-slow))
			   (not (eq? c 'too-slow))
			   (equivalent? e d)
			   (equivalent? e c)))))
	  '((<=> (⊕ a b c d) (<=> (⊕ a b) (⊕ c d)))
	    (⊕ (<=> a (⊕ b c)) (<=> (⊕ a d) (and b c)) (<=> c d) (=> (⊕ a b) d))
	    (and (<=> (⊕ a b) (⊕ c d)) (<=> (⊕ a c) (⊕ b d)) (⊕ a b c d))))

(unless {failures = 0}
  (error "check-many-variables : results wrong or too slow :" failures))

) ; end module
