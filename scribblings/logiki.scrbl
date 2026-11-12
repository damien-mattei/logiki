#lang scribble/manual

@(require (for-label racket/base logiki))

@title{λογικι (logiki) : symbolic propositional logic in Scheme+}
@author{Damien Mattei}

@defmodule[logiki]

logiki computes symbolically with formulas of propositional logic : it puts a formula in disjunctive or conjunctive
normal form, and finds its @emph{minimal} disjunctive or conjunctive form with the Quine-McCluskey and Petrick methods.
It is written in @hyperlink["https://docs.racket-lang.org/Scheme-PLUS-for-Racket/index.html"]{Scheme+}, and the
formulas can be written in prefix or in infix notation.

@section{Installation}

@commandline{raco pkg install logiki}

Then, in a module :

@verbatim|{
#lang reader SRFI-105
(module example racket
  (require Scheme+)
  (require logiki)
  (display (infix-symb-min-cnf '{b and d or a and not d})))
}|

displays @racketresult[((a ∨ d) ∧ (b ∨ ¬d))].

@section{Formulas}

A formula is a symbol (a variable), a boolean (@racket[#t], @racket[#f], or the symbols @racket['T] and @racket['F]), or a
list whose first element is an operator :

@tabular[#:sep @hspace[2]
 (list (list @bold{operator} @bold{symbols})
       (list "conjunction" @racket[and AND ·])
       (list "disjunction" @racket[or OR ＋])
       (list "negation" @racket[not NOT])
       (list "exclusive or" @racket[xor XOR ⊕])
       (list "implication" @racket[=> ⟹])
       (list "equivalence" @racket[<=> ⟺]))]

@racket[and], @racket[or] and @racket[⊕] take any number of arguments, and @racket[<=>] two or more
(@racket['(<=> a b c)] is @racket['(<=> a (<=> b c))]). The constants inside a formula are simplified first :
@racket['(and a (not F))] is @racket['a], @racket['(=> F x)] is @racket[#t]. The variables are case sensitive :
@racket['a] and @racket['A] are two variables.

In a Scheme+ source file
(@racketfont{#lang reader SRFI-105}), a quoted formula can be written in infix notation, with the precedence of the
operators : @racket['{not a and b or c}] is read @racket['(or (and (not a) b) c)], and @racket['{A ⊕ B ⊕ Ci}] is read
@racket['(⊕ A B Ci)]. In a quoted formula, only the curly brackets are infix : the parentheses stay lists in prefix
notation, so write @racket['{{b and d} or {a and not d}}] or @racket['{b and d or a and not d}], not
@racket['{(b and d) or (a and not d)}].

The results are formulas in prefix notation, or, for the procedures whose name contains @racketfont{infix}, the same
formulas in infix notation :
@itemlist[
 @item{@racketfont{infix-symb} : with the symbols @racket[∧ ∨ ¬], for example @racketresult[((a ∧ ¬b) ∨ c)] ;}
 @item{@racketfont{infix-symb-bool} : with the symbols of boolean algebra @racket[· ＋] (＋ is the fullwidth plus, U+FF0B) and a bar over a negated
       variable, for example @racketresult[((a · d̅) ＋ (b · d))] ;}
 @item{@racketfont{infix} : with the words @racket[and or] and @racket[!] for the negation, for example
       @racketresult[((a and !b) or c)].}]

@section{Normal forms}

@defproc[(dnf [formula any/c]) any/c]{
The disjunctive normal form of a formula with binary operators (use @racket[dnf-n-arity-simp] for any number of
arguments).
@racketblock[(dnf '(and (or a b) (not c)))]
gives @racketresult[(or (and a (not c)) (and b (not c)))].}

@defproc[(cnf [formula any/c]) any/c]{
The conjunctive normal form of a formula with binary operators.
@racketblock[(cnf '(or (and a b) (and c d)))]
gives @racketresult[(and (and (or a c) (or a d)) (and (or b c) (or b d)))].}

@defproc[(dnf-n-arity-simp [formula any/c]) any/c]{
The disjunctive normal form, with operators of any number of arguments, simplified (antilogies, useless terms).}

@defproc[(cnf-n-arity-simp [formula any/c]) any/c]{
The conjunctive normal form, with operators of any number of arguments, simplified (tautologies, useless clauses).}

@defproc[(maximal-dnf [formula any/c]) any/c]{
The maximal (canonical) disjunctive normal form of any formula : the disjunction of its minterms, each one with all
the variables, once.
@racketblock[(maximal-dnf '(or (and a b) c))]
gives @racketresult[(or (and a b c) (and a b (not c)) (and a (not b) c) (and (not a) b c) (and (not a) (not b) c))].}

@defproc[(maximal-cnf [formula any/c]) any/c]{
The maximal (canonical) conjunctive normal form of any formula : the conjunction of its maxterms, each one with all
the variables, once.
@racketblock[(maximal-cnf '(or (and a b) c))]
gives @racketresult[(and (or a b c) (or a (not b) c) (or (not a) b c))].}

@deftogether[(@defproc[(infix-symb-max-dnf [formula any/c]) any/c]
              @defproc[(infix-symb-max-cnf [formula any/c]) any/c])]{
The maximal forms in infix notation.
@racketblock[(infix-symb-max-cnf '(<=> a b))]
gives @racketresult[((a ∨ ¬b) ∧ (¬a ∨ b))].}

@deftogether[(@defproc[(dnf-infix-symb [formula any/c]) any/c]
              @defproc[(dnf-infix [formula any/c]) any/c]
              @defproc[(cnf-infix-symb [formula any/c]) any/c]
              @defproc[(cnf-infix [formula any/c]) any/c])]{
The simplified normal forms in infix notation.
@racketblock[(cnf-infix-symb '(or (and b d) (and a (not d))))]
gives @racketresult[((a ∨ b) ∧ (a ∨ d) ∧ (b ∨ ¬d))] : a normal form, but not a minimal one, the clause
@racketresult[(a ∨ b)] is useless (see @racket[minimal-cnf]).}

@section{Minimal forms}

@defproc[(minimal-dnf [formula any/c]) any/c]{
The minimal disjunctive normal form : the least terms, then the least literals.
@racketblock[
(minimal-dnf '(or (and (not a) b (not c) d) (and (not a) b c d)
                  (and a b (not c) (not d)) (and a b (not c) d)
                  (and a b c (not d)) (and a b c d)
                  (and a (not b) (not c) (not d)) (and a (not b) c (not d))))]
gives @racketresult[(or (and a (not d)) (and b d))].}

@defproc[(minimal-cnf [formula any/c]) any/c]{
The minimal conjunctive normal form : the least clauses, then the least literals.
@racketblock[(minimal-cnf '(or (and b d) (and a (not d))))]
gives @racketresult[(and (or a d) (or b (not d)))].

A tautology gives @racket[#t] and an antilogy @racket[#f], as with @racket[minimal-dnf].}

@deftogether[(@defproc[(infix-symb-min-dnf [formula any/c]) any/c]
              @defproc[(infix-symb-bool-min-dnf [formula any/c]) any/c]
              @defproc[(infix-min-dnf [formula any/c]) any/c]
              @defproc[(infix-symb-min-cnf [formula any/c]) any/c]
              @defproc[(infix-symb-bool-min-cnf [formula any/c]) any/c]
              @defproc[(infix-min-cnf [formula any/c]) any/c])]{
The minimal forms in infix notation. In infix, a tautology is @racketresult[T] and an antilogy @racketresult[F].
@racketblock[
(infix-symb-min-dnf '{not a and not b and not c and not d
                      or not a and not b and not c and d
                      or not a and not b and c and not d
                      or not a and b and not c and d
                      or not a and b and c and not d
                      or not a and b and c and d
                      or a and not b and not c and not d
                      or a and not b and not c and d
                      or a and not b and c and not d
                      or c and not d})]
gives @racketresult[((¬a ∧ b ∧ d) ∨ (¬b ∧ ¬c) ∨ (c ∧ ¬d))], and @racket[infix-symb-min-cnf] gives for the same formula
@racketresult[((¬a ∨ ¬b ∨ ¬d) ∧ (b ∨ ¬c ∨ ¬d) ∧ (¬b ∨ c ∨ d))].

@racketblock[(infix-symb-min-dnf '(⊕ (· B1 B0) (· C1 (⊕ B1 B0))))]
gives @racketresult[((B0 ∧ B1) ∨ (B0 ∧ C1) ∨ (B1 ∧ C1))], the carry of an adder, and
@racketblock[(infix-symb-min-dnf '(and (=> (and p q) r) (=> (not (and p q)) r)))]
gives @racketresult[r].

With the other notations :
@racketblock[(infix-symb-bool-min-cnf '(or (and b d) (and a (not d))))]
gives @racketresult[((a ＋ d) · (b ＋ d̅))], and
@racketblock[(infix-min-cnf '(or (and b d) (and a (not d))))]
gives @racketresult[((a or d) and (b or !d))].}

@subsection{The method}

The minimal disjunctive form is computed with the method of Quine and McCluskey :
@itemlist[#:style 'ordered
 @item{the minterms of the formula are found : the conjunctions of all the variables, written in binary,
       @racketresult[(1 0 x 1)] standing for @racketresult[(a ∧ ¬b ∧ d)]. They come from the terms of the disjunctive
       normal form when the distribution gives few terms, otherwise from the truth table : the distribution explodes
       with the structure of the formula, the truth table with the number of variables (2@superscript{n} lines) ;}
 @item{the minterms are unified two by two, by groups of the same weight, until the prime implicants ;}
 @item{the essential prime implicants are found with the table of the prime implicants and of the minterms ;}
 @item{if they do not express all the minterms, the method of Petrick chooses the cheapest set of non essential prime
       implicants that express the others (the least prime implicants, then the least literals). The product of sums of
       Petrick is expanded one sum after the other with absorption (X + XY = X).}]

The minimal conjunctive form uses the same method on the maxterms : the maxterms of a function are the minterms of its
negation, read on the truth table of the function. The minimal conjunctive form of the function is the dual
(De Morgan) of the minimal disjunctive form of its negation.

The number of minterms grows as 2@superscript{n} with the number n of variables.

@section{Truth table}

@defproc[(formula-value [formula any/c] [environment list?]) boolean?]{
The value of a formula for an environment, an association list of the variables and their boolean values.
@racketblock[(formula-value '(=> a (⊕ b T)) '((a . #t) (b . #f)))]
gives @racket[#t].}

@defproc[(truth-table [formula any/c]) list?]{
The truth table of a formula : the list of its lines, each one a pair of an assignment of the variables and of the
value of the formula. The variables are in alphabetic order, the first one being the most significant.
@racketblock[(truth-table '(=> a b))]
gives @racketresult[(((#f #f) . #t) ((#f #t) . #t) ((#t #f) . #f) ((#t #t) . #t))].}

@defproc[(display-truth-table [formula any/c]) void?]{
Displays the truth table of a formula. @racket[(display-truth-table '(=> a b))] displays :
@verbatim|{
a b | (=> a b)
0 0 | 1
0 1 | 1
1 0 | 0
1 1 | 1
}|}

@deftogether[(@defproc[(minterm-numbers [formula any/c]) list?]
              @defproc[(maxterm-numbers [formula any/c]) list?])]{
The numbers of the lines of the truth table where the formula is true (its minterms), where it is false (its
maxterms). @racket[(minterm-numbers '(=> a b))] gives @racketresult[(0 1 3)] and
@racket[(maxterm-numbers '(=> a b))] gives @racketresult[(2)].}

@deftogether[(@defproc[(minterms->formula [numbers list?] [variables list?]) any/c]
              @defproc[(maxterms->formula [numbers list?] [variables list?]) any/c])]{
The function given by the numbers of its minterms, Σm(...), or of its maxterms, ΠM(...), in canonical form.
@racketblock[(minterms->formula '(0 1 3) '(a b))]
gives @racketresult[(or (and (not a) (not b)) (and (not a) b) (and a b))], and
@racketblock[(maxterms->formula '(2) '(a b))]
gives @racketresult[(or (not a) b)].}

@defproc[(minimal-dnf-of-minterms [numbers list?] [variables list?]) any/c]{
The minimal disjunctive normal form of the function given by the numbers of its minterms.
@racketblock[(minimal-dnf-of-minterms '(0 1 2 5 6 7) '(a b c))]
gives @racketresult[(or (and a b) (and (not a) (not c)) (and (not b) c))].}

@deftogether[(@defproc[(tautology? [formula any/c]) boolean?]
              @defproc[(antilogy? [formula any/c]) boolean?]
              @defproc[(satisfiable? [formula any/c]) boolean?])]{
Is the formula always true, always false, true for one assignment at least ?
@racket[(tautology? '(=> (and (=> p q) p) q))] gives @racket[#t].}

@deftogether[(@defproc[(equivalent? [formula1 any/c] [formula2 any/c]) boolean?]
              @defproc[(implies? [formula1 any/c] [formula2 any/c]) boolean?])]{
Have the two formulas the same value for every assignment of their variables ? Is the second one true each time the
first one is ? @racket[(equivalent? '(=> a b) '(or (not a) b))] gives @racket[#t], and
@racket[(implies? 'a '(and a b))] gives @racket[#f].}

@defproc[(models [formula any/c]) list?]{
The models of a formula : the assignments that make it true, as association lists.
@racketblock[(models '(and a (not b)))]
gives @racketresult[(((a . #t) (b . #f)))].}

@section{Conversions}

@deftogether[(@defproc[(prefix->infix-symb [formula any/c]) any/c]
              @defproc[(prefix->infix-symb-bool [formula any/c]) any/c]
              @defproc[(prefix->infix [formula any/c]) any/c])]{
A formula in prefix notation written in infix notation.
@racketblock[(prefix->infix-symb '(or (and a (not b)) c))]
gives @racketresult[((a ∧ ¬b) ∨ c)].}

@defproc[(n-arity [formula any/c]) any/c]{
A formula with binary operators written with operators of any number of arguments :
@racket['(or a (or b c))] becomes @racket['(or a b c)].}

@section{Tests}

@defproc[(logic-test) boolean?]{
Runs 23 tests : normal forms, minimal forms and maximal forms of formulas, compared to their exact result, with
@racketresult[EXACT] or @racketresult[DIFFER] displayed for each one. Returns @racket[#t] if all are exact.}

The directory @filepath{tests} of the package contains @filepath{logic-test.rkt}, and @filepath{check-petrick.rkt} which
compares @racket[minimal-dnf] and @racket[minimal-cnf] to a computation by brute force on the 256 functions of 3
variables and on 3000 functions of 4 variables, then checks @racket[minimal-dnf], @racket[minimal-cnf] and
@racket[maximal-dnf] on 1200 random formulas against their truth table, and @filepath{check-formulas.rkt} which checks
all the procedures of this manual and the infix results on 2100 random formulas written with all the synonyms of the
operators and the constants, with three sets of names of variables (@racket[a b c d e], @racket[B₁₂ x10 x2 Ci B₃],
@racket[a A b B c]) : @exec{raco test tests}.

@section{License}

logiki is free software, under the GNU General Public License, version 3 or (at your option) any later version.
