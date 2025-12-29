; Test negative literals: (or (not a) (not b)) - both negated
; Only satisfiable when at least one of a, b is false
(set-logic QF_NRA)

(declare-const a Bool)
(declare-const b Bool)
(declare-const x Real)

(assert (>= x 0))
(assert (<= x 1))

; If a=true, x must be > 10 (impossible)
; If b=true, x must be < -10 (impossible)
; Need a=false or b=false
(assert (or
  (and (not a) (>= x 0))
  (and (not b) (<= x 1))
))

(check-sat)
