;; From https://github.com/dreal/dreal4/issues/198
(set-logic QF_NRA)
(set-option :worklist-fixpoint true)
(declare-const r31415926 Real)
(declare-const r31415927 Real)
(assert (> r31415926 r31415927))
(check-sat)
(declare-const r13 Real)
(push 1)
(pop 1)
(assert (or (> r31415926 r31415927) (= r13 0.0)))
(check-sat)

