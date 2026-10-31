* §4.2, a genuine divergence between readers rather than a rule. Read literally
* `UP -3` with the default lower bound 0 is `0 <= X <= -3`, infeasible. CPLEX
* opens the lower bound to -infinity only when the upper is STRICTLY below zero,
* and at exactly `UP 0` keeps it at 0 -- a third behaviour. The rule taken here
* is warned per instance.
ROWS
 N  C
 L  R
COLUMNS
    X         C            1.0        R            1.0
RHS
    RHS       R            100.0
BOUNDS
 UP BND       X            -3.0
ENDATA
