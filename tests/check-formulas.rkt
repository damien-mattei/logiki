#lang reader SRFI-105

;; raco test : random formulas with all the synonyms of the operators (AND · OR ＋ ➕ NOT XOR ⊕ ⟹ ⟺ ...) and the
;; constants (T F #t #f) , on 3 to 5 variables , with three sets of names of variables (a b c d e , B₁₂ x10 x2 Ci B₃ ,
;; a A b B c) : dnf , cnf , dnf-n-arity-simp , cnf-n-arity-simp , minimal-dnf , minimal-cnf , maximal-dnf , maximal-cnf ,
;; the infix results , truth-table , minterms->formula , maxterms->formula , the predicates and the models checked
;; against the truth table and the normal form , and the minimality up to 4 variables.
;; The test fails if one result is wrong. The normal forms computed by distribution (dnf , cnf , dnf-n-arity-simp ,
;; cnf-n-arity-simp) are skipped for a formula if they take more than 3 s (a slowness , not an error).

(module check-formulas racket

(require Scheme+)
(require logiki)

(define (bits m n)
  (build-list n (λ (i) (if (bitwise-bit-set? m {n - 1 - i}) 1 0))))

;; the expression of a function given by the list of its minterms
(define (bench-minterms->formula mts vars)
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
  {f <- (bench-minterms->formula mts vars)}
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
  {f <- (bench-minterms->formula mts vars)}
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



;; the truth value of a formula with all the operators and constants of logiki
(define (truth e env)
  (condx ((memq e '(T True ■ #t)) #t)
	 ((memq e '(F False □ #f)) #f)
	 ((symbol? e) (cdr (assq e env)))
	 (exec {op <- (car e)} {xs <- (map (λ (x) (truth x env)) (cdr e))})
	 ((memq op '(not NOT)) (not (car xs)))
	 ((memq op '(and AND ·)) (andmap values xs))
	 ((memq op '(or OR ＋ ➕)) (ormap values xs))
	 ((memq op '(xor XOR ⊕)) (odd? (count values xs)))
	 ((memq op '(=> ⟹)) (or (not (car xs)) (cadr xs)))
	 ((memq op '(<=> ⟺)) (eq? (car xs) (cadr xs)))
	 (else (error "truth : unknown operator" e))))

(define var-names (make-parameter '(a b c d e)))
(define-syntax-rule (all-vars) (var-names))
(define constants (make-parameter 0)) ; 0 : constants allowed , -1 : no constant
(define synonyms (make-parameter #t))

(define (table e nv)
  {vs <- (take (all-vars) nv)}
  (map (λ (m) (truth e (map (λ (v b) (cons v {b = 1})) vs (bits m nv)))) (range {2 ** nv})))

(define (minterms-of-table tb) (filter (λ (m) (list-ref tb m)) (range (length tb))))

;; random formula : operators with their synonyms , constants , nv variables
(define (rnd lst) (list-ref lst (random (length lst))))
(define (random-formula depth nv)
  (condx ((or {depth = 0} {(random 4) = 0})
	  (condx ({(random 12) = (constants)} (rnd '(T F #t #f)))
		 (else (let ((v (rnd (take (all-vars) nv)))) (if {(random 2) = 0} v (list (rnd (if (synonyms) '(not NOT) '(not))) v))))))
	 (exec {op <- (rnd (if (synonyms) '(and AND · or OR ＋ ➕ not NOT xor XOR ⊕ => ⟹ <=> ⟺) '(and or not ⊕ => <=>)))})
	 ((memq op '(not NOT)) (list op (random-formula {depth - 1} nv)))
	 ((memq op '(=> ⟹ <=> ⟺)) (list op (random-formula {depth - 1} nv) (random-formula {depth - 1} nv)))
	 (else (cons op (build-list {2 + (random 2)} (λ (i) (random-formula {depth - 1} nv)))))))

;; structure : a disjunctive normal form with the operators and , or , not
(define (term? e) (or (literal? e) (memq e '(T F #t #f)) (and (pair? e) (eq? (car e) 'and) (andmap literal? (cdr e)))))
(define (dnf? e) (or (term? e) (and (pair? e) (eq? (car e) 'or) (andmap term? (cdr e)))))
;; binary dnf (dnf , cnf : binary operators allowed , nested and/or of the same operator)
(define (nested-dnf? e) ;; or of ands of literals , nested
  (define (nterm? e) (or (literal? e) (memq e '(T F #t #f)) (and (pair? e) (eq? (car e) 'and) (andmap nterm? (cdr e)))))
  (or (nterm? e) (and (pair? e) (eq? (car e) 'or) (andmap nested-dnf? (cdr e)))))
(define (nested-cnf? e)
  (define (nclause? e) (or (literal? e) (memq e '(T F #t #f)) (and (pair? e) (eq? (car e) 'or) (andmap nclause? (cdr e)))))
  (or (nclause? e) (and (pair? e) (eq? (car e) 'and) (andmap nested-cnf? (cdr e)))))


;; the truth value of an infix result of logiki : a list operand op operand ... with one kind of operator , the
;; negated variables written ¬x (symb) , x̅ (bool , a combining overline U+0305) or !x (words)
(define (literal-truth s env)
  (condx ((memq s '(T ■)) #t)
	 ((memq s '(F □)) #f)
	 (exec {str <- (symbol->string s)})
	 ((and {(string-length str) > 1} (char=? (string-ref str 0) #\¬)) (not (cdr (assq (string->symbol (substring str 1)) env))))
	 ((and {(string-length str) > 1} (char=? (string-ref str 0) #\!)) (not (cdr (assq (string->symbol (substring str 1)) env))))
	 ((for/or ((c str)) (char=? c #\u0305)) (not (cdr (assq (string->symbol (list->string (filter (λ (c) (not (char=? c #\u0305))) (string->list str)))) env))))
	 (else (cdr (assq s env)))))

(define (infix-truth e env)
  (condx ((symbol? e) (literal-truth e env))
	 ((boolean? e) e)
	 ((null? (cdr e)) (infix-truth (car e) env))
	 (exec {op <- (cadr e)}
	       {operands <- (let loop ((l e)) (if (null? l) '() (cons (car l) (if (null? (cdr l)) '() (loop (cddr l))))))}
	       {vals <- (map (λ (x) (infix-truth x env)) operands)})
	 ((memq op '(∧ · and)) (andmap values vals))
	 ((memq op '(∨ ＋ or)) (ormap values vals))
	 (else (error "infix-truth : unknown operator" op e))))

(define (infix-table e nv)
  {vs <- (take (all-vars) nv)}
  (map (λ (m) (infix-truth e (map (λ (v b) (cons v {b = 1})) vs (bits m nv)))) (range {2 ** nv})))

;; the procedures computed on the truth table (no limit of time) : the minimal forms , the maximal forms , the truth
;; table , the functions given by numbers , the predicates and the models
(define (check-by-table e nv minimality?)
  {tb <- (table e nv)}
  {mts <- (minterms-of-table tb)}
  {bad <- '()}
  (define (note kind r) {bad <- (cons (list kind r) bad)})
  (define (try thunk) (with-handlers ((exn:fail? (λ (x) (list 'ERROR (exn-message x))))) (thunk)))
  (define (err? r) (and (pair? r) (eq? (car r) 'ERROR)))
  (define (same? r) (equal? (table r nv) tb))
  (define (kind name suffix) (string->symbol (format "~a-~a" name suffix)))
  ;; the minimal forms
  (for-each (λ (name f form?)
	      {r <- (try (λ () (f e)))}
	      (condx ((err? r) (note (kind name "error") r))
		     ((not (form? r)) (note (kind name "not-normal-form") r))
		     ((not (same? r)) (note (kind name "wrong") r))))
	    '(minimal-dnf minimal-cnf)
	    (list minimal-dnf minimal-cnf)
	    (list dnf? cnf?))
  (when minimality?
    {r <- (try (λ () (minimal-dnf e)))}
    (when (and (not (err? r)) (same? r) (cost<? (minimal-cost mts nv) (cost r))) (note 'minimal-dnf-not-minimal r))
    {r <- (try (λ () (minimal-cnf e)))}
    (when (and (not (err? r)) (same? r) (cnf? r)
	       (cost<? (minimal-cost (filter (λ (m) (not (memv m mts))) (range {2 ** nv})) nv) (cost-cnf r)))
      (note 'minimal-cnf-not-minimal r)))
  ;; the infix results
  (for-each (λ (name f)
	      {r <- (try (λ () (f e)))}
	      (condx ((err? r) (note (kind name "error") r))
		     (exec {it <- (try (λ () (infix-table r nv)))})
		     ((err? it) (note (kind name "unreadable") (list r it)))
		     ((not (equal? it tb)) (note (kind name "wrong") r))))
	    '(infix-symb-min-dnf infix-symb-min-cnf infix-symb-bool-min-dnf infix-symb-bool-min-cnf infix-min-dnf infix-min-cnf infix-symb-max-dnf infix-symb-max-cnf)
	    (list infix-symb-min-dnf infix-symb-min-cnf infix-symb-bool-min-dnf infix-symb-bool-min-cnf infix-min-dnf infix-min-cnf infix-symb-max-dnf infix-symb-max-cnf))
  ;; the variables of the formula as logiki sees them , and its truth table
  {vs <- (try (λ () (collect-variables e)))}
  {tt <- (try (λ () (truth-table e)))}
  (condx ((err? tt) (note 'truth-table-error tt))
	 ((not {(length tt) = 2 ** (length vs)}) (note 'truth-table-size tt))
	 ((not (andmap (λ (line) (eq? (cdr line) (truth e (map cons vs (car line))))) tt))
	  (note 'truth-table-wrong tt)))
  ;; the maximal forms : right , each term or clause with all the variables , once , as many as the lines of the table
  (for-each (λ (name f form? operator numbers)
	      {r <- (try (λ () (f e)))}
	      {ns <- (try (λ () (numbers e)))}
	      (condx ((err? r) (note (kind name "error") r))
		     ((err? ns) (note (kind name "numbers-error") ns))
		     ((not (form? r)) (note (kind name "not-normal-form") r))
		     ((not (same? r)) (note (kind name "wrong") r))
		     ((memq r '(#t #f)) (unless {(null? ns) or (null? vs)} (note (kind name "boolean") r)))
		     (exec {terms <- (if (and (pair? r) (eq? (car r) operator)) (cdr r) (list r))})
		     ((not (andmap (λ (t) {(literals-of-term t) = (length vs)}) terms)) (note (kind name "not-complete") r))
		     ((not {(length terms) = (length (remove-duplicates terms))}) (note (kind name "duplicate") r))
		     ((not {(length terms) = (length ns)}) (note (kind name "number-of-terms") r))))
	    '(maximal-dnf maximal-cnf)
	    (list maximal-dnf maximal-cnf)
	    (list dnf? cnf?)
	    '(or and)
	    (list minterm-numbers maxterm-numbers))
  ;; the function given back by the numbers of its minterms , of its maxterms
  (for-each (λ (name numbers build)
	      {r <- (try (λ () (build (numbers e) vs)))}
	      (condx ((err? r) (note (kind name "error") r))
		     ((not (same? r)) (note (kind name "wrong") r))))
	    '(minterms->formula maxterms->formula)
	    (list minterm-numbers maxterm-numbers)
	    (list minterms->formula maxterms->formula))
  ;; the predicates
  (for-each (λ (name f expected)
	      {r <- (try (λ () (f e)))}
	      (condx ((err? r) (note (kind name "error") r))
		     ((not (eq? r expected)) (note (kind name "wrong") r))))
	    '(tautology? antilogy? satisfiable?)
	    (list tautology? antilogy? satisfiable?)
	    (list (andmap values tb) (not (ormap values tb)) (and (ormap values tb) #t)))
  ;; the models : each one makes the formula true , as many as the true lines of the table of logiki
  {ms <- (try (λ () (models e)))}
  (condx ((err? ms) (note 'models-error ms))
	 ((not (andmap (λ (m) (truth e m)) ms)) (note 'models-wrong ms))
	 ((and (not (err? tt)) (not {(length ms) = (count cdr tt)})) (note 'models-number ms)))
  ;; a formula is equivalent to its minimal forms , implied by each term of its minimal disjunctive form , and not
  ;; equivalent to its negation
  {equivalences <- (try (λ () (and (equivalent? e (minimal-dnf e))
				   (equivalent? e (minimal-cnf e))
				   (implies? (minimal-dnf e) e)
				   (not (equivalent? e (list 'not e))))))}
  (unless (eq? equivalences #t) (note 'equivalent?-wrong equivalences))
  bad)

;; the normal forms computed by transformation (distribution) : they can be slow , under a limit of time
(define (check-by-distribution e nv)
  {tb <- (table e nv)}
  {bad <- '()}
  (define (note kind r) {bad <- (cons (list kind r) bad)})
  (define (try thunk) (with-handlers ((exn:fail? (λ (x) (list 'ERROR (exn-message x))))) (thunk)))
  (define (err? r) (and (pair? r) (eq? (car r) 'ERROR)))
  (define (same? r) (equal? (table r nv) tb))
  (define (kind name suffix) (string->symbol (format "~a-~a" name suffix)))
  ;; dnf and cnf take binary operators
  {eb <- (try (λ () (n-arity-operation->binary-operation e)))}
  (for-each (λ (name f form? formula)
	      {r <- (try (λ () (f formula)))}
	      (condx ((err? r) (note (kind name "error") r))
		     ((not (form? r)) (note (kind name "not-normal-form") r))
		     ((not (same? r)) (note (kind name "wrong") r))))
	    '(dnf cnf dnf-n-arity-simp cnf-n-arity-simp)
	    (list dnf cnf dnf-n-arity-simp cnf-n-arity-simp)
	    (list nested-dnf? nested-cnf? dnf? cnf?)
	    (list eb eb e e))
  (for-each (λ (name f)
	      {r <- (try (λ () (f e)))}
	      (condx ((err? r) (note (kind name "error") r))
		     (exec {it <- (try (λ () (infix-table r nv)))})
		     ((err? it) (note (kind name "unreadable") (list r it)))
		     ((not (equal? it tb)) (note (kind name "wrong") r))))
	    '(dnf-infix-symb cnf-infix-symb)
	    (list dnf-infix-symb cnf-infix-symb))
  bad)

(define (check-by-distribution-in-time e nv)
  {result <- 'slow}
  {th <- (thread (λ () {result <- (check-by-distribution e nv)}))}
  (if (sync/timeout 3 th)
      result
      ($> (kill-thread th)
	  'slow)))

{problems <- 0}

(define (campaign k depth nv minimality? seed)
  (random-seed seed)
  {slow <- 0}
  {all <- (append-map (λ (i)
			{e <- (random-formula depth nv)}
			{r-table <- (check-by-table e nv minimality?)}
			{r <- (check-by-distribution-in-time e nv)}
			(map (λ (b) (cons e b))
			     (if (eq? r 'slow)
				 ($> {slow <- slow + 1} r-table)
				 (append r-table r))))
		      (range k))}
  (printf "~a formulas , depth ~a , ~a variables : problems ~a , normal forms by distribution skipped (over 3 s) ~a\n" k depth nv (length all) slow)
  {problems <- problems + (length all)}
  (for-each (λ (kind)
	      {ex <- (filter (λ (b) (eq? (cadr b) kind)) all)}
	      (printf "   ~a : ~a   e.g. ~s -> ~s\n" kind (length ex) (car (car ex)) (caddr (car ex))))
	    (remove-duplicates (map cadr all))))

(for-each (λ (names)
	    (parameterize ((var-names names))
	      (printf "variables ~a\n" names)
	      (campaign 300 2 3 #t 1)
	      (campaign 300 3 4 #t 2)
	      (campaign 100 3 5 #f 3)))
	  '((a b c d e) (B₁₂ x10 x2 Ci B₃) (a A b B c)))

(unless {problems = 0}
  (error "check-formulas : wrong results :" problems))

) ; end module
