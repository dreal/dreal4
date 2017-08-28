(set-logic QF_NRA)
(declare-fun x () Real [0, 8])
(declare-fun forall y () Real [0, 7.5])
(assert
 (forall
  ((y Real))
  (or
   (<=
    (+ (^ (- x 2) 2)
       (^ (- y 2) 2))
    9)
   (<=
    (+ (^ (- x 5) 2)
       (^ (- y 5) 2))
    9))))
(check-sat)
(exit)
