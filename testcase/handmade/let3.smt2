(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(assert (let ((s1 (= a a)))
    (let ((s2 (and s1 (not s1)))) s2)
))
(check-sat)
