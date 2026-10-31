; ADT-LIA shape from the official track: datatype operations are interpreted
; background symbols; Reach is the only relation whose interpretation is sought.
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-fun Reach (List) Bool)
(assert (forall ((xs List)) (=> (= xs nil) (Reach xs))))
(assert (forall ((xs List) (ys List))
  (=> (and (Reach xs) (= ys (cons 0 xs))) (Reach ys))))
(assert (forall ((xs List)) (=> (and (Reach xs) (< (head xs) 0)) false)))
(check-sat)
