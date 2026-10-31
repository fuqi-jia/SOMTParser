(set-logic QF_FPLRA)
(declare-fun y () (_ FloatingPoint 11 53))
(assert (fp.eq y ((_ to_fp 11 53) RNE 2)))
(check-sat)
