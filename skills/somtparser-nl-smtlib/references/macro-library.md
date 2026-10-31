# Shared macros and HIR reuse

The authoritative constructor API is `somtparser.hir.hir_api()` in the live
request. Prefer these existing implementations over a second handwritten library.

| Meaning | Native HIR expression | Direct SMT meaning |
|---|---|---|
| All different | `{"op":"all_different","args":[...]}` or CP `all_different` | `distinct` over the exact scalar cells |
| Boolean count | `{"cp":"count_true","items":[...]}` | Sum of `ite b 1 0` |
| At most one | `{"cp":"at_most_one","items":[...]}` | Boolean count <= 1 |
| Absolute value | `{"op":"abs","args":[e]}` (Int or Real) | Exact conditional on the sign |
| Integer min/max | `{"cp":"minimum|maximum","items":[...]}` | Exact nested `ite`; nonempty inputs |
| No overlap | `{"cp":"no_overlap","starts":[...],"durations":[...]}` | Pairwise interval non-overlap with identical endpoint/zero-duration semantics |
| Cumulative | CP `cumulative` with starts/durations/demands/capacity | Exact native event-time lowering; do not guess a horizon |
| Table | CP `table` with explicit `positive` polarity | Membership in allowed/forbidden tuples |
| Cardinality | CP `global_cardinality`, `among` | Exact occurrence/member counts |
| Finite sum/forall/exists | `fold` over an explicit half-open range | Exact bounded semantics; the backend may expand or retain guarded quantifiers |

Read the live catalog for exact fields and sorts. For example `no_overlap` uses
integer starts and fixed nonnegative durations; it is not an arbitrary optional
continuous-time interval primitive. Presence/alternatives need explicit modeling.
Whole finite arrays, rows and columns have different constructor shapes.

The generator adds only these compositional conveniences to HIR. Their spelling
is structured JSON, `{"macro":name,"args":[...]}`, expanded **before** native
schema/type validation; no string evaluation and no `macro(...) | raw(...)` grammar.

| Macro | Args | Exact expansion |
|---|---|---|
| `makespan` | nonempty `[[start,duration], ...]` | Balanced exact maximum of completion times using `ite`, not merely upper bounds |
| `distance_to` | `[expression,target]` | Native `abs(sub(expression,target))` |
| `weighted_sum` | `[[weight,expression], ...]` | Native sum of products; weight signs preserved |
| `in_range` | `[expression,lo,hi]` | Inclusive conjunction `expression >= lo` and `expression <= hi` |
| `exactly`, `at_most`, `at_least` | `[k,[Boolean expressions...]]` | Compare native `count_true` to k |

Arguments are HIR expressions, including explicitly sorted literals. The live
HIR schema describes the expanded model; the request's macro extension describes
this preprocessing notation. Unknown names/arity and empty makespan are errors.

`makespan` remains exact if maximized, constrained elsewhere or compared as a
cost relation. A minimization-only epigraph formulation is not substituted.
No `bounded` macro adds a guessed range to prevent unboundedness. No macro called
`strict_min` claims that a strict real bound attains an optimum. These are source
semantics, not formatting options.

Objective direction/order remains in the actual model fields. `lex`, `pareto`
and `box` are not term macros and are available only where the selected route's
schema, frontend and dialect actually implement them.
