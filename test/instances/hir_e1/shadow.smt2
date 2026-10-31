(set-logic LIA)
(declare-fun p (Int) Bool)
(assert (forall ((j Int)) (or (p j) (exists ((j Int)) (p j)))))
(check-sat)
