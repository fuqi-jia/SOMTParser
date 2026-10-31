\ lp.md §4.1's scaling rescue is MOOT: ExprKind::LIT_REAL landed and keeps a
\ decimal exactly, so nothing is scaled and there is no scale factor that must
\ be recorded. 0.1 has no finite binary expansion; a double would lose it.
Minimize
 obj: 0.1 x + 0.25 y
Subject To
 c1: 0.5 x + 1.25 y <= 3.75
End
