(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (<= -5.12 x))
(assert (<= x     -5.119492))
(assert (<= 1.167154 y))
(assert (<= y     1.1672140509))
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
