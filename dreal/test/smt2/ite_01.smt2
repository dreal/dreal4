(set-logic QF_NRA)
(declare-fun x () Real [0, 10])
(declare-fun y () Real [0, 10])
(assert (= (ite (> x y) x y)
           y))
(check-sat)
(exit)


;; `F[ite(C, t₁, t₂)]` => `(C ⇒ F[t₁]) ∧ (C ⇒ F[t₂])`
