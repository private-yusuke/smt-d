(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(assert (let ((v (= a a))) (and v (not v))))
(check-sat)
