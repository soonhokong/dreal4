; Test underscore variant of produce_models option
(set-logic QF_NRA)
(set-option :produce_models true)
(declare-fun x () Real)
(assert (<= 0 x))
(assert (<= x 1))
(check-sat)
