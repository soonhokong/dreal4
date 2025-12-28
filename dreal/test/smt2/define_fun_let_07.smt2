; Regression test: three calls to function with nested let
(set-logic QF_NRA)

(define-fun square_plus_one ((x Real)) Real
  (let ((sq (* x x)))
    (let ((result (+ sq 1))) result)))

(define-fun R1 () Real (square_plus_one 2.0))
(define-fun R2 () Real (square_plus_one 3.0))
(define-fun R3 () Real (square_plus_one 4.0))

; R1=5, R2=10, R3=17
(assert (= R1 5.0))
(assert (= R2 10.0))
(assert (= R3 17.0))

(check-sat)
