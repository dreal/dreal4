(set-logic QF_NRA)
(declare-fun x1 () Real [0.0, 7.0])
(declare-fun z () Real)
(assert
 (forall ((x2 Real [0.0, 7.0]))
         (<=
          z
          (- (* (sin x2) (^ x2 2))
             (* (cos x2) x2)))))
(assert (= z
	   (- (* (sin x1) (^ x1 2))
             (* (cos x1) x1))))
(check-sat)
(exit)
