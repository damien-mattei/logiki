#lang reader SRFI-105

;; raco test : the tests of logic-test (formulas put in normal form and in minimal form , compared to their exact
;; result) , the test fails if one of them differs

(module logic-test racket

  (require Scheme+)
  (require logiki)

  (unless (logic-test)
    (error "logic-test : a result differs from the exact one (see DIFFER above)"))

  ) ; end module
