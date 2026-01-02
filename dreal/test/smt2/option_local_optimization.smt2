; Test local-optimization option
(set-logic QF_NRA)
(set-option :local-optimization true)
(declare-fun x () Real)
(assert (<= 0 x))
(assert (<= x 1))
(check-sat)
