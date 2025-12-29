; Test single negative literal: (not a) only
; Satisfiable only when a=false
(set-logic QF_NRA)

(declare-const a Bool)
(declare-const x Real)

(assert (>= x 0))
(assert (<= x 1))

; Force a to be false via theory constraint
(assert (not a))
(assert (>= x 0.5))

(check-sat)
