\ §2.3, §4.4: a semi-continuous variable is `x = 0 OR l <= x <= u` -- a
\ DISJUNCTION, not the interval [0, u]. The interval reading admits every value
\ between 0 and l, which is precisely the range the modeller excluded.
Minimize
 obj: x
Subject To
 c1: x <= 9
Bounds
 2 <= x <= 8
Semi-Continuous
 x
End
