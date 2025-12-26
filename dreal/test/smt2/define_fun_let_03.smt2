; Regression test: nested let where inner references outer binding
(set-logic QF_NRA)

(define-fun nested_ref ((a Real) (b Real)) Real
  (let ((sum (+ a b)))
    (let ((result (* sum sum)))
      result)))

(define-fun TEST () Real (nested_ref 2.0 3.0))

; TEST should equal (2+3)^2 = 25
(assert (= TEST 25.0))

(check-sat)
