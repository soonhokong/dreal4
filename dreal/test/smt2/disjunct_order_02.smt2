; Regression test for disjunct order bug - swapped order
; (or B A) should also be SAT
(set-logic QF_NRA)

(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const x Real)
(declare-const v Real)

(assert (or b1 b2))
(assert (not (and b1 b2)))

(assert (= v (ite b1 1.0 2.0)))

; Same as disjunct_order_01 but with swapped disjunct order
(assert (or
  (and b2 (>= x 2) (<= x 3) (= v 2.0))
  (and b1 (>= x 0) (<= x 1) (= v 1.0))
))

(check-sat)
