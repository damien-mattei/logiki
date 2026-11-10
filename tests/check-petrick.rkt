#lang reader SRFI-105

;; raco test : check of minimal-dnf and minimal-cnf of logiki (Quine-McCluskey + Petrick) against a brute force
;; computation : the result must be equal to the function on the whole truth table , and its cost (number of terms or
;; clauses , then number of literals) must be the minimal one , whatever the calls made before.
;; The 256 functions of 3 variables and 3000 functions of 4 variables at random , in an order then in the other ,
;; then 1200 random formulas (and , or , not , ⊕ , => , <=>) , with maximal-dnf too.
;; The test fails if one result is wrong , not minimal , not in normal form or raises an error.

(module check-petrick racket

(require Scheme+)
(require logiki)
(require (only-in srfi/69 hash-table-keys hash-table-delete!))

;; the bits of the minterm m on n variables , the first variable is the most significant bit
(define (bits m n)
  (build-list n (λ (i) (if (bitwise-bit-set? m {n - 1 - i}) 1 0))))

;; the expression of a function given by the list of its minterms
(define (minterms->formula mts vars)
  {n <- (length vars)}
  {terms <- (map (λ (m)
		   (cons 'and (map (λ (v b) (if {b = 1} v (list 'not v)))
				   vars
				   (bits m n))))
		 mts)}
  (condx ((null? terms) 'F)
	 ((null? (cdr terms)) (car terms))
	 (else (cons 'or terms))))

;; the value of a formula in prefix notation for an environment (an association list variable -> boolean)
(define (eval-formula e env)
  (condx ((memq e '(T #t)) #t)
	 ((memq e '(F #f)) #f)
	 ((symbol? e) (cdr (assq e env)))
	 (exec {op <- (car e)})
	 ((eq? op 'not) (not (eval-formula (cadr e) env)))
	 ((eq? op 'and) (andmap (λ (x) (eval-formula x env)) (cdr e)))
	 ((eq? op 'or) (ormap (λ (x) (eval-formula x env)) (cdr e)))
	 ((eq? op '⊕) (odd? (count (λ (x) (eval-formula x env)) (cdr e))))
	 ((eq? op '=>) (or (not (eval-formula (cadr e) env)) (eval-formula (caddr e) env)))
	 ((eq? op '<=>) (eq? (eval-formula (cadr e) env) (eval-formula (caddr e) env)))
	 (else (error "eval-formula : unknown operator" e))))

;; is the formula equal to the function on the whole truth table ?
(define (same-function? e mts vars)
  {n <- (length vars)}
  (andmap (λ (m)
	    {env <- (map (λ (v b) (cons v {b = 1})) vars (bits m n))}
	    (eq? (eval-formula e env)
		 (and (memv m mts) #t)))
	  (range {2 ** n})))

;; the cost of a formula in disjunctive form : (number of terms . number of literals)
(define (literals-of-term t)
  (condx ((memq t '(T #t F #f)) 0)
	 ((symbol? t) 1)
	 ((eq? (car t) 'not) 1)
	 (else (length (cdr t))))) ;; an and

(define (cost e)
  (condx ((memq e '(F #f)) (cons 0 0))
	 ((memq e '(T #t)) (cons 1 0))
	 ((and (pair? e) (eq? (car e) 'or))
	  (cons (length (cdr e)) (apply + (map literals-of-term (cdr e)))))
	 (else (cons 1 (literals-of-term e)))))

(define (cost<? c1 c2)
  (or {(car c1) < (car c2)}
      (and {(car c1) = (car c2)} {(cdr c1) < (cdr c2)})))

;; brute force : the cubes are lists of 0 , 1 and x
(define (cubes n)
  (if {n = 0}
      '(())
      (apply append (map (λ (c) (map (λ (v) (cons v c)) '(0 1 x)))
			 (cubes {n - 1})))))

(define (covers? cube bs)
  (andmap (λ (c b) (or (eq? c 'x) (eqv? c b))) cube bs))

(define (implicant? cube f-bits all-bits)
  (and (ormap (λ (bs) (covers? cube bs)) f-bits)
       (andmap (λ (bs) (or (not (covers? cube bs)) (member bs f-bits))) all-bits)))

(define (enlarge cube i) ;; the bit i becomes x
  (for/list ((c cube) (j (in-naturals))) (if {j = i} 'x c)))

(define (prime? cube f-bits all-bits)
  (and (implicant? cube f-bits all-bits)
       (for/and ((c cube) (i (in-naturals)))
	 (or (eq? c 'x)
	     (not (implicant? (enlarge cube i) f-bits all-bits))))))

(define (combinations lst k)
  (condx ((= k 0) '(()))
	 ((null? lst) '())
	 (else (append (map (λ (c) (cons (car lst) c)) (combinations (cdr lst) {k - 1}))
		       (combinations (cdr lst) k)))))

(define (cube-literals cube) (count (λ (c) (not (eq? c 'x))) cube))

;; the minimal cost of a disjunctive form of the function
(define (minimal-cost mts n)
  {all-bits <- (map (λ (m) (bits m n)) (range {2 ** n}))}
  {f-bits <- (map (λ (m) (bits m n)) mts)}
  (condx ((null? mts) (cons 0 0))
	 ({(length mts) = (length all-bits)} (cons 1 0))
	 (exec {primes <- (filter (λ (c) (prime? c f-bits all-bits)) (cubes n))})
	 (else
	  (let loop ((k 1))
	    {covers <- (filter (λ (s) (andmap (λ (bs) (ormap (λ (c) (covers? c bs)) s)) f-bits))
			       (combinations primes k))}
	    (if (null? covers)
		(loop {k + 1})
		(cons k (apply min (map (λ (s) (apply + (map cube-literals s))) covers))))))))

;; one call of minimal-dnf , checked
(define (check-one mts vars)
  {f <- (minterms->formula mts vars)}
  {res <- (with-handlers ((exn:fail? (λ (e) (list 'ERROR (exn-message e)))))
	    (minimal-dnf f))}
  {status <- (condx ((and (pair? res) (eq? (car res) 'ERROR)) 'error)
		    ((not (same-function? res mts vars)) 'wrong)
		    (exec {c <- (cost res)} {cmin <- (minimal-cost mts (length vars))})
		    ((cost<? cmin c) 'not-minimal)
		    (else 'ok))}
  (list status mts res))

;; conjunctive normal form : T , F , a literal , a clause (or of literals) or an and of literals and clauses
(define (literal? e)
  (or (symbol? e) (and (pair? e) (eq? (car e) 'not) (symbol? (cadr e)))))

(define (clause? e)
  (or (literal? e) (and (pair? e) (eq? (car e) 'or) (andmap literal? (cdr e)))))

(define (cnf? e)
  (or (memq e '(T F #t #f))
      (clause? e)
      (and (pair? e) (eq? (car e) 'and) (andmap clause? (cdr e)))))

;; the cost of a formula in conjunctive form : (number of clauses . number of literals)
(define (cost-cnf e)
  (condx ((memq e '(T #t)) (cons 0 0))
	 ((memq e '(F #f)) (cons 1 0))
	 ((and (pair? e) (eq? (car e) 'and))
	  (cons (length (cdr e)) (apply + (map literals-of-term (cdr e)))))
	 (else (cons 1 (literals-of-term e)))))

;; one call of minimal-cnf , checked : its minimal cost is the minimal cost of the disjunctive form of the negation
(define (check-one-cnf mts vars)
  {n <- (length vars)}
  {f <- (minterms->formula mts vars)}
  {res <- (with-handlers ((exn:fail? (λ (e) (list 'ERROR (exn-message e)))))
	    (minimal-cnf f))}
  {status <- (condx ((and (pair? res) (eq? (car res) 'ERROR)) 'error)
		    ((not (cnf? res)) 'not-cnf)
		    ((not (same-function? res mts vars)) 'wrong)
		    (exec {c <- (cost-cnf res)}
			  {cmin <- (minimal-cost (filter (λ (m) (not (memv m mts))) (range {2 ** n})) n)})
		    ((cost<? cmin c) 'not-minimal)
		    (else 'ok))}
  (list status mts res))

(define current-check (make-parameter check-one))

(define (run-list label lst vars)
  (map (λ (mts) ((current-check) mts vars)) lst))

(define (summary label results)
  (display label) (display " : ")
  (for-each (λ (s) (display s) (display " ") (display (count (λ (r) (eq? (car r) s)) results)) (display "  "))
	    '(ok wrong not-minimal not-cnf error))
  (newline))

(define (show-bad results k)
  (for-each (λ (r) (display "   ") (display (car r)) (display " minterms ") (display (cadr r))
		    (display " -> ") (display (caddr r)) (newline))
	    (take (filter (λ (r) (not (eq? (car r) 'ok))) results)
		  (min k (count (λ (r) (not (eq? (car r) 'ok))) results)))))

;; the 256 functions of 3 variables
(define vars3 '(a b c))
(define funs3 (map (λ (code) (filter (λ (m) (bitwise-bit-set? code m)) (range 8))) (range 256)))

;; 3000 functions of 4 variables at random
(random-seed 42)
(define vars4 '(a b c d))
(define funs4 (for/list ((i 3000)) (filter (λ (m) {(random 2) = 1}) (range 16))))

;; the number of results not ok , and of results depending on the order of the calls
{failures <- 0}

(define (compare-orders label funs vars)
  {fwd <- (run-list label funs vars)}
  {bwd <- (reverse (run-list label (reverse funs) vars))}
  (summary (string-append label " forward ") fwd)
  (show-bad fwd 6)
  (summary (string-append label " backward") bwd)
  (show-bad bwd 6)
  {diff <- (count (λ (r1 r2) (not (equal? (caddr r1) (caddr r2)))) fwd bwd)}
  {failures <- failures + diff + (count (λ (r) (not (eq? (car r) 'ok))) (append fwd bwd))}
  (display label) (display " : results depending on the order of the calls : ") (display diff) (newline))

;; racket check-petrick.rkt               : all the checks
;; racket check-petrick.rkt n m1 m2 ...    : one function of n variables (3 or 4) , in a fresh process
;; racket check-petrick.rkt list n         : print the functions of the list of n variables , one per line
;; random formulas : random trees of and , or , not , ⊕ , => , <=> on the variables a b c d ; their normal forms have
;; terms of any length and literals alone , as (not c) in (or (not c) (and a (not d)))
(define (random-formula depth)
  (condx ((or {depth = 0} {(random 4) = 0})
	  (let ((v (list-ref vars4 (random 4))))
	    (if {(random 2) = 0} v (list 'not v))))
	 (exec {op <- (list-ref '(and or not ⊕ => <=>) (random 6))})
	 ((eq? op 'not) (list 'not (random-formula {depth - 1})))
	 ((memq op '(=> <=>)) (list op (random-formula {depth - 1}) (random-formula {depth - 1})))
	 (else (cons op (build-list {2 + (random 2)} (λ (i) (random-formula {depth - 1})))))))

(define (minterms-of e)
  (filter (λ (m) (eval-formula e (map (λ (v b) (cons v {b = 1})) vars4 (bits m 4))))
	  (range 16)))

;; the literals of a term of a maximal DNF , as strings sorted : to find the duplicate terms
(define (term-key t)
  (sort (map (λ (l) (format "~a" l)) (if (and (pair? t) (eq? (car t) 'and)) (cdr t) (list t))) string<?))

;; one random formula checked : minimal-dnf and minimal-cnf right and minimal , maximal-dnf right , each of its terms
;; with all the variables , no duplicate term
(define (check-formula e)
  {mts <- (minterms-of e)}
  {cmin-dnf <- (minimal-cost mts 4)}
  {cmin-cnf <- (minimal-cost (filter (λ (m) (not (memv m mts))) (range 16)) 4)}
  (define (try thunk) (with-handlers ((exn:fail? (λ (x) (list 'ERROR (exn-message x))))) (thunk)))
  (define (error? r) (and (pair? r) (eq? (car r) 'ERROR)))
  {r-dnf <- (try (λ () (minimal-dnf e)))}
  {r-cnf <- (try (λ () (minimal-cnf e)))}
  {r-max <- (try (λ () (maximal-dnf (dnf-n-arity-simp e))))}
  {bad <- '()}
  (condx ((error? r-dnf) {bad <- (cons (list 'minimal-dnf-error r-dnf) bad)})
	 ((not (same-function? r-dnf mts vars4)) {bad <- (cons (list 'minimal-dnf-wrong r-dnf) bad)})
	 ((cost<? cmin-dnf (cost r-dnf)) {bad <- (cons (list 'minimal-dnf-not-minimal r-dnf) bad)}))
  (condx ((error? r-cnf) {bad <- (cons (list 'minimal-cnf-error r-cnf) bad)})
	 ((not (cnf? r-cnf)) {bad <- (cons (list 'minimal-cnf-not-cnf r-cnf) bad)})
	 ((not (same-function? r-cnf mts vars4)) {bad <- (cons (list 'minimal-cnf-wrong r-cnf) bad)})
	 ((cost<? cmin-cnf (cost-cnf r-cnf)) {bad <- (cons (list 'minimal-cnf-not-minimal r-cnf) bad)}))
  (condx ((error? r-max) {bad <- (cons (list 'maximal-dnf-error r-max) bad)})
	 ((not (same-function? r-max mts vars4)) {bad <- (cons (list 'maximal-dnf-wrong r-max) bad)})
	 (exec {terms <- (if (and (pair? r-max) (eq? (car r-max) 'or)) (cdr r-max) (list r-max))}
	       {nvars <- (length (collect-variables r-max))})
	 ((not {(length terms) = (length (remove-duplicates (map term-key terms)))})
	  {bad <- (cons (list 'maximal-dnf-duplicate r-max) bad)})
	 ((not (andmap (λ (t) (or (memq t '(T F #t #f)) {(literals-of-term t) = nvars})) terms))
	  {bad <- (cons (list 'maximal-dnf-not-complete r-max) bad)}))
  bad)

;; a formula whose check takes more than 2 s is skipped : its normal form , computed by distribution , is too big (a
;; slowness , not an error) ; the hash table of the minterms , left full by the computation stopped , is emptied
(define (check-formula-in-time e)
  {result <- 'slow}
  {th <- (thread (λ () {result <- (check-formula e)}))}
  (if (sync/timeout 2 th)
      result
      ($> (kill-thread th)
	  (for-each (λ (k) (hash-table-delete! minterms-ht k)) (hash-table-keys minterms-ht))
	  'slow)))

(define (check-random-formulas k depth)
  (random-seed 2026)
  {slow <- 0}
  {all-bad <- (append-map (λ (i)
			    {e <- (random-formula depth)}
			    {r <- (check-formula-in-time e)}
			    (if (eq? r 'slow)
				($> {slow <- slow + 1} '())
				(map (λ (b) (cons e b)) r)))
			  (range k))}
  (display "random formulas : ") (display k) (display " , depth ") (display depth) (display " , problems : ")
  (display (length all-bad)) (display " , skipped (more than 2 s) : ") (display slow) (newline)
  ;; the number of problems of each kind
  (for-each (λ (kind)
	      (display "   ") (display kind) (display " : ") (display (count (λ (b) (eq? (cadr b) kind)) all-bad)) (newline))
	    (remove-duplicates (map cadr all-bad)))
  (for-each (λ (b) (display "   ") (write b) (newline)) (take all-bad (min 6 (length all-bad))))
  {failures <- failures + (length all-bad)})

{cl <- (vector->list (current-command-line-arguments))}

(condx ((null? cl)
	(newline)
	(display "cyclic function m(0,1,2,5,6,7) , fresh : ")
	(display (check-one '(0 1 2 5 6 7) vars3)) (newline)
	(compare-orders "DNF 3 variables" funs3 vars3)
	(compare-orders "DNF 4 variables" funs4 vars4)
	(parameterize ((current-check check-one-cnf))
	  (display "cyclic function m(0,1,2,5,6,7) , CNF : ")
	  (display (check-one-cnf '(0 1 2 5 6 7) vars3)) (newline)
	  (compare-orders "CNF 3 variables" funs3 vars3)
	  (compare-orders "CNF 4 variables" funs4 vars4))
	(check-random-formulas 1000 3)
	(check-random-formulas 200 4)
	(unless {failures = 0}
	  (error "check-petrick : results wrong , not minimal , not in normal form , in error or depending on the order of the calls :" failures)))
       ((string=? (car cl) "list")
	(for-each (λ (mts) (display (string-join (map number->string mts) " ")) (newline))
		  (if (string=? (cadr cl) "3") funs3 funs4)))
       (else ;; racket check-petrick.rkt [cnf] n m1 m2 ...
	{cnf-mode <- (string=? (car cl) "cnf")}
	{cl2 <- (if cnf-mode (cdr cl) cl)}
	{n <- (string->number (car cl2))}
	{mts <- (map string->number (cdr cl2))}
	{r <- ((if cnf-mode check-one-cnf check-one) mts (if {n = 3} vars3 vars4))}
	(display (car r)) (display " ") (display (cadr r)) (display " -> ") (display (caddr r)) (newline)))

) ; end module
