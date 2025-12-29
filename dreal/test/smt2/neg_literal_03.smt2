; Test negative literals: (or (not b) (not a)) - reversed order
; Same as neg_literal_02 but with swapped order
(set-logic QF_NRA)

(declare-const a Bool)
(declare-const b Bool)
(declare-const x Real)

(assert (>= x 0))
(assert (<= x 1))

(assert (or
  (and (not b) (<= x 1))
  (and (not a) (>= x 0))
))

(check-sat)
