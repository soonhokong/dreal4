; Regression test: let in both ite branches, multiple calls
(set-logic QF_NRA)

(define-fun branch ((x Real)) Real
  (let ((base (* x 2)))
    (ite (> base 10)
         (let ((high (+ base 100))) high)
         (let ((low (- base 100))) low))))

(define-fun R1 () Real (branch 10.0))
(define-fun R2 () Real (branch 3.0))

; R1: base=20>10, high=120. R2: base=6<=10, low=-94
(assert (= R1 120.0))
(assert (= R2 -94.0))

(check-sat)
