(set-logic QF_LRA)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= (+ x y) 2))
(assert (<= x 0))
(assert (<= (/ y 2) 1.5))
(check-sat)
(exit)