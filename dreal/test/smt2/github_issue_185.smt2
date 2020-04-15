;; From https://github.com/dreal/dreal4/issues/185
(set-logic QF_NRA)
(set-option :worklist-fixpoint true)
(declare-const r0 Real)
(declare-const r1 Real)
(assert (= (/ 0.0 (* (- r1) r0 r0)) r0))
(check-sat)
