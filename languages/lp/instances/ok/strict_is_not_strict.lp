\ §2.4: `<` and `<=` mean the SAME THING. Linear programming has no strict
\ inequality, and a frontend emitting Op::LT produces a model whose feasible
\ region excludes its own boundary -- which is where an LP optimum usually is.
Minimize
 obj: x
Subject To
 c1: x < 5
 c2: x > 1
End
