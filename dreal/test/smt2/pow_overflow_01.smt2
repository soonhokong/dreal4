; Test pow overflow: pow(2, 1024) overflows to +inf
; The pruning should return [DBL_MAX, +inf], making this SAT
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x (^ 2.0 1024.0)))
(check-sat)
(exit)
