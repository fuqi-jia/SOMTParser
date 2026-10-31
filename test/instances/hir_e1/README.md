# E1 HIR-route regression inputs

These seven minimal SMT-LIB scripts were retrieved from panda7's
`/tmp/jiafq-hir/` on 2026-10-15 following the 420-task E1 pilot. The reported
source families are SPARK AUFBVDTNIRA and UltimateAutomizer BVFPLRA.

`shadow2`/`shadow3`, `fpterm`, and `realnum2` reproduce the three HIR-route
failures. `shadow`, `realnum`, and `realnum3` retain the already-working nested
shadowing and constant-rounding-mode controls. The regression checks both
Parser→HIR→Parser and the public translation pipeline.
