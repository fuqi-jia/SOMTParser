\ §2.3: Binary is integer in {0,1} and it OVERRIDES any Bounds entry. Letting
\ the Bounds line win would widen the domain of exactly the variables a MIP
\ model most relies on.
Minimize
 obj: b
Subject To
 c1: b >= 0
Bounds
 -10 <= b <= 10
Binary
 b
End
