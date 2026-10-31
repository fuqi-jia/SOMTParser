(set-logic LIA)
(synth-fun id ((v Int)) Int
  ((Start Int))
  ((Start Int ((Variable Int)))))
(declare-var x Int)
(constraint (= (id x) x))
(check-synth)
