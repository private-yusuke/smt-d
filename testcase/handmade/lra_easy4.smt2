(set-logic QF_LRA)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= x 0))
(assert (<= y 3))
(check-sat)
(exit)