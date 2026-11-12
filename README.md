# λογικι (logiki)

Symbolic computation of propositional logic, written in [Scheme+](https://github.com/damien-mattei/Scheme-PLUS-for-Racket) for Racket :

- disjunctive and conjunctive normal forms ;
- **minimal** disjunctive and conjunctive normal forms, with the Quine-McCluskey and Petrick methods ;
- maximal (canonical) disjunctive and conjunctive normal forms ;
- truth table, functions given by the numbers of their minterms or maxterms, tautology, equivalence, models ;
- formulas in prefix or in infix notation (`{a and not b or c}`), with the operators `and or not xor => <=>` and their
  symbols `· ＋ ⊕ ⟹ ⟺` ;
- results in prefix notation, or in infix notation with the symbols `∧ ∨ ¬`, the symbols of boolean algebra, or words.

## Changes of version 21.2

The truth table : `truth-table`, `display-truth-table`, `formula-value`, `minterm-numbers`, `maxterm-numbers`, and the
functions given by the numbers of their minterms or maxterms, `minterms->formula`, `maxterms->formula`,
`minimal-dnf-of-minterms`. The maximal conjunctive normal form `maximal-cnf`, and `maximal-dnf` takes any formula.
The predicates `tautology?`, `antilogy?`, `satisfiable?`, `equivalent?`, `implies?`, and `models`.

`minimal-dnf` and `minimal-cnf` find the minterms in two ways : by the disjunctive normal form when the distribution
gives few terms (as before, fast even with 20 variables), otherwise on the truth table. They are no more slow for the
formulas with `⊕` or `<=>` whose normal form by distribution is big (before, several seconds with 4 variables).

## Changes of version 21.1

The Or of the notation of boolean algebra (`infix-symb-bool-min-dnf` ...) is now ＋ (U+FF0B , fullwidth plus) :
`((a ＋ d) · (b ＋ d̅))`. The heavy plus used before (U+2795 , often displayed as an emoji) is still read.

## Installation

```
raco pkg install logiki
```

## Example

```scheme
#lang reader SRFI-105
(module example racket
  (require Scheme+)
  (require logiki)
  (display (infix-symb-min-cnf '{b and d or a and not d})))
```

displays `((a ∨ d) ∧ (b ∨ ¬d))`.

| procedure | formula | result |
|---|---|---|
| `minimal-dnf` | `'(or (and b d) (and a (not d)))` | `(or (and a (not d)) (and b d))` |
| `minimal-cnf` | `'(or (and b d) (and a (not d)))` | `(and (or a d) (or b (not d)))` |
| `cnf-infix-symb` (not minimal) | `'(or (and b d) (and a (not d)))` | `((a ∨ b) ∧ (a ∨ d) ∧ (b ∨ ¬d))` |
| `infix-symb-min-dnf` | `'(⊕ (· B1 B0) (· C1 (⊕ B1 B0)))` | `((B0 ∧ B1) ∨ (B0 ∧ C1) ∨ (B1 ∧ C1))` |
| `infix-symb-bool-min-cnf` | `'(or (and b d) (and a (not d)))` | `((a ＋ d) · (b ＋ d̅))` |
| `infix-min-cnf` | `'(or (and b d) (and a (not d)))` | `((a or d) and (b or !d))` |

The minimal conjunctive form is computed with the Quine-McCluskey method on the maxterms : the maxterms of a function
are the minterms of its negation, so the minimal conjunctive form is the dual (De Morgan) of the minimal disjunctive
form of the negation.

## Documentation

The manual is in `scribblings/logiki.scrbl` and, once the package is installed, on
[docs.racket-lang.org](https://docs.racket-lang.org/logiki/index.html).

## Tests

```
raco test tests
```

`tests/logic-test.rkt` runs the 23 tests of `(logic-test)`. `tests/check-petrick.rkt` compares `minimal-dnf` and
`minimal-cnf` to a computation by brute force on the 256 functions of 3 variables and on 3000 functions of 4 variables,
then checks `minimal-dnf`, `minimal-cnf` and `maximal-dnf` on 1200 random formulas (`and or not ⊕ => <=>`) against
their truth table. `tests/check-formulas.rkt` checks all the procedures and the infix results on 2100 random formulas
written with all the synonyms of the operators (`AND · OR ＋ NOT XOR ⟹ ⟺`) and the constants (`T F #t #f`), with
names of variables such as `B₁₂`, `x10`, and `a` and `A` together.

## License

GNU General Public License , version 3 or (at your option) any later version : see `LICENSE`.

Damien Mattei
