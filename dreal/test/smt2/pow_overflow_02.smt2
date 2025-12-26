; Test pow overflow with constraint: x > DBL_MAX should be SAT
; because pow(2, 1024) is mathematically larger than DBL_MAX
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x (^ 2.0 1024.0)))
(assert (> x 1e308))
(check-sat)
(exit)
