(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(assert (= a 2))
(assert (= b 3))
(assert
  (let ((a
         (let ((b (+ 2 b)))
           (* a b)))
        (b (* 10 b)))
    (and (= a 10) (= b 30))))
(check-sat)
(exit)
