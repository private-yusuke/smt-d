(set-logic QF_LRA)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(check-sat)
(exit)