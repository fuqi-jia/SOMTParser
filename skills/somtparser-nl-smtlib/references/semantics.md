# Source-to-model semantics

Inventory each clause's entities, scope, domains, units, conditions, required
relation and objective role. This can be an internal checklist; do not extend
the fixed response schema. Keep all instance data and source index conventions.

| Source meaning | SMT construction | Common error |
|---|---|---|
| Unknown count | `Int` with source-derived bounds | Treating a decision variable as missing input |
| Continuous quantity | `Real` with exact constants | Imposing integrality or using floating point |
| Selection/truth | `Bool`; count with `(ite p 1 0)` | Adding Boolean values directly |
| If P then Q; P only if Q | `(=> P Q)` | Reversed or unconditional constraint |
| P iff Q | `(= P Q)` for Booleans | Keeping only one implication |
| At least / at most | `>=` / `<=` | Replacing either by equality |
| Below / above | `<` / `>` unless explicit context says otherwise | Relaxing strictness to match gold |
| Exactly k conditions | Sum Boolean indicators equals k | Assuming mutual exclusion |
| An available alternative | Guarded permission or choice member | Requiring every permitted alternative |
| Named individuals | Uninterpreted constants; disequality if stated | Assuming distinct names mean distinct objects |

Combine compatible units only; convert using exact source-known factors. Do not
guess a conversion, duration, time horizon or big-M bound.

`Int` is an unbounded mathematical integer. A machine integer needs source-given
width and overflow semantics; distinguish signed/unsigned bit-vector operators.
Floating point needs format and rounding semantics, and is not a mathematical
real. String constraints use their string theory operations. For an uncommon
theory, verify representative syntax against both the installed frontend and
the chosen solver before launching large experiments; neither implies the other.

SMT arrays are total. A finite array therefore needs index guards or explicit
scalar cells. `select`/`store` mean lookup/functional update, not source bounds.
Empty aggregates and partial operations need explicit source semantics.

A hard cost bound and minimizing that cost can coexist. Contradictory clauses
may legitimately yield UNSAT; do not discard them. Redundancy, complexity and
ordinary boundary cases are not ambiguities. `unresolved` is for materially
different readings left unsettled by source/context. Never hide a genuine one
in `assumptions` to make the model compile.

Source spans are half-open Unicode code-point offsets, not byte offsets. Compute
them against unchanged text. A link fragment is copied from the final SMT
program, not from the natural-language sentence; recompute links after repair.
