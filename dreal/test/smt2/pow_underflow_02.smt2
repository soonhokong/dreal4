; Regression test: pow underflow with very large exponent
; 0.5^2000 should be positive (not underflow to 0)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x (^ 0.5 2000.0)))
(assert (> x 0))
(check-sat)
