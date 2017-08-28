(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (<= -5.12 x))
(assert (<= x     5.12))
(assert (<= -5.12 y))
(assert (<= y     5.12))
(assert (<= -10   z))
(assert (<= z     10))
(assert (=
         z
         (+
          (^
           (+
            (- 1.5 x)
            (* x y))
           2)
          (^
           (+
            (- 2.25 x)
            (^ (* x y) 2))
           2)
          (^
           (+
            (- 2.625 x)
            (^ (* x y) 3))
           2))))
(check-sat)
(exit)
