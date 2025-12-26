; Regression test: define-fun with let expression
; Tests that let bindings inside define-fun are correctly substituted
(set-logic QF_NRA)

(define-fun A ((x_1 Real) (y_1 Real) (x_2 Real) (y_2 Real)) Real
  (let ((dx (- x_2 x_1))
        (dy (- y_2 y_1)))
    (+ dx dy)))

(define-fun A_TEST () Real (A 1.0 2.0 3.0 4.0))

; A_TEST should equal (3-1) + (4-2) = 4
(assert (= A_TEST 4.0))

(check-sat)
