; Test negative literal: (not a) in first position of disjunction
; Formula: (or (not a) b) with constraints that make a=false the solution
(set-logic QF_NRA)

(declare-const a Bool)
(declare-const b Bool)
(declare-const x Real)

; x in [0, 1]
(assert (>= x 0))
(assert (<= x 1))

; If a is true, x must be > 10 (impossible given bounds)
; If a is false, satisfiable
(assert (or
  (and (not a) (>= x 0))
  (and b (> x 10))
))

(check-sat)
