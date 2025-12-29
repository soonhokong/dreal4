; Test single negative literal: (not b) only
(set-logic QF_NRA)

(declare-const b Bool)
(declare-const x Real)

(assert (>= x 0))
(assert (<= x 1))

(assert (not b))
(assert (<= x 0.5))

(check-sat)
