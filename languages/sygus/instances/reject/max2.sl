; The archetypal SyGuS instance: synthesise a function from a grammar.
(set-logic LIA)
(synth-fun max2 ((x Int) (y Int)) Int
  ((Start Int)) ((Start Int ((Variable Int) 0 1 (+ Start Start) (ite StartBool Start Start))))
)
(declare-var x Int)
(declare-var y Int)
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(check-synth)
