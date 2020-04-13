;; From https://github.com/dreal/dreal4/issues/194
(set-logic QF_NRA)
(set-option :worklist-fixpoint true)
(declare-fun _substvar_261_ () Bool)
(declare-const v13 Bool)
(declare-const r6 Real)
(declare-const r9 Real)
(assert (or (and v13 (or v13 (= r6 r9))) _substvar_261_))
(check-sat)
