\ lp.md's first obligation, and the one that matters. Neither x nor y has a
\ Bounds entry, and both are still constrained to be non-negative -- that is
\ the LP format's semantics, from linear programming's own tradition, and no
\ line here says it. Omitting it yields a strictly weaker model: more feasible
\ points, so a better "optimum", reported as exact().
Minimize
 obj: x + y
Subject To
 c1: x + y >= 3
End
