; Test worklist-fixpoint option
(set-logic QF_NRA)
(set-option :worklist-fixpoint true)
(declare-fun x () Real)
(assert (<= 0 x))
(assert (<= x 1))
(check-sat)
