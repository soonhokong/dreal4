; Regression test for disjunct order bug
; (or A B) should be SAT - tests that Boolean literals controlling ITE branches
; are properly included in learned clauses
(set-logic QF_NRA)

(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const x Real)
(declare-const v Real)

; Exactly one of b1, b2 is true
(assert (or b1 b2))
(assert (not (and b1 b2)))

; v depends on which boolean is true
(assert (= v (ite b1 1.0 2.0)))

; (or A B) where A and B have different constraints
(assert (or
  (and b1 (>= x 0) (<= x 1) (= v 1.0))
  (and b2 (>= x 2) (<= x 3) (= v 2.0))
))

(check-sat)
