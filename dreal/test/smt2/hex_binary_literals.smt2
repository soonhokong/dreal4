; Test hexadecimal and binary literals
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x #xFF))
(assert (= y #b1010))
(assert (= (+ x y) 265))
(check-sat)
