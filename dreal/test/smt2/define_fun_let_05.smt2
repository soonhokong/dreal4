; Regression test: nested let with inner referencing outer, multiple calls
(set-logic QF_NRA)

(define-fun nested ((x Real)) Real
  (let ((a (+ x 1)))
    (let ((b (* a 2))) b)))

(define-fun R1 () Real (nested 5.0))
(define-fun R2 () Real (nested 10.0))

; R1 = (5+1)*2 = 12, R2 = (10+1)*2 = 22
(assert (= R1 12.0))
(assert (= R2 22.0))

(check-sat)
