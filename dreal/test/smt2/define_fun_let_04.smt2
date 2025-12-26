; Regression test: triple nested let in define-fun
(set-logic QF_NRA)

(define-fun triple ((x Real)) Real
  (let ((a (+ x 1)))
    (let ((b (* a 2)))
      (let ((c (- b 3)))
        c))))

(define-fun TEST () Real (triple 5.0))

; TEST should equal ((5+1)*2)-3 = 9
(assert (= TEST 9.0))

(check-sat)
