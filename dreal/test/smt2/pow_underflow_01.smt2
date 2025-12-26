; Regression test: pow underflow with constant base
; 0.5^1075 should be positive (not underflow to 0)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x (^ 0.5 1075.0)))
(assert (> x 0))
(check-sat)
