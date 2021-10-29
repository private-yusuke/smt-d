(set-logic QF_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun a () U)
(assert (let ((s1 (= a a)))
    (let ((s2 (or s1 (not s1)))) s2)
))
(check-sat)
