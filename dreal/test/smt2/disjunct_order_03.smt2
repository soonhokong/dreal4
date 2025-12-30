; Regression test for disjunct order bug - more complex ITE
; Tests Boolean matrix controlling ITE branches
(set-logic QF_NRA)

(declare-const x1 Real) (assert (= x1 -5.0))
(declare-const x2 Real) (assert (= x2 -10.0))

(declare-const b_0_0 Bool)
(declare-const b_0_1 Bool)
(declare-const b_1_0 Bool)
(declare-const b_1_1 Bool)

; Boolean matrix constraints
(assert (or b_0_0 b_0_1))
(assert (or b_1_0 b_1_1))
(assert (not (and b_0_0 b_0_1)))
(assert (not (and b_1_0 b_1_1)))
(assert (not (and b_0_0 b_1_0)))
(assert (not (and b_0_1 b_1_1)))
(assert (or b_0_0 b_1_0))
(assert (or b_0_1 b_1_1))

(declare-const vx0 Real)
(declare-const vx1 Real)
(assert (= vx0 (ite b_0_0 x1 x2)))
(assert (= vx1 (ite b_1_0 x1 x2)))

(declare-const choice Int)

(assert (or
  (and (= choice 0) (>= vx1 -6.0) (<= vx1 -4.0))
  (and (= choice 1) (>= (- vx1 vx0) -6.0) (<= (- vx1 vx0) 0.0))
))

(check-sat)
