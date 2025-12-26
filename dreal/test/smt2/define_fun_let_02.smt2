; Regression test: nested let in define-fun
(set-logic QF_NRA)

(define-fun nested ((a Real) (b Real)) Real
  (let ((sum (+ a b)))
    (let ((doubled (* sum 2)))
      doubled)))

(define-fun RESULT () Real (nested 3.0 4.0))

; RESULT should equal (3+4)*2 = 14
(assert (= RESULT 14.0))

(check-sat)
