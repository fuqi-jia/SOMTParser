# Finite constraint and application encodings

| Requirement | Exact pattern and preconditions |
|---|---|
| All-different | `(distinct x0 ... xn)` over scalar cells; zero/one item is true |
| Count | Sum `(ite condition 1 0)` over the full source index set |
| Exactly / at-most / at-least k | Compare that sum using `=`, `<=`, `>=` |
| Among | Count membership in a finite set; repeated set values do not multiply counts |
| Global cardinality | One occurrence equation per specified value; restrict all values only for a closed domain |
| Allowed table | Disjunction of conjunctions matching every allowed tuple |
| Forbidden table | Negate membership in the forbidden tuple set |
| Element | Finite scalar selection or `select` with source index guards |
| Finite universal / existential | Conjunction / disjunction over exactly the source set |

Empty allowed tables are false, forbidden tables true. Empty finite universals
are true and existentials false. Do not emit malformed empty arithmetic terms.

Preserve every data row, repeated activity and source index base. Rows, columns
and flattened matrices are different views; document exact mappings. For routing,
route position `route[i]` differs from city identity: `arrival[route[i]]` cannot
be replaced with `arrival[i]` without a justified representation mapping.

For scheduling:

- Guard optional activities by presence. If two present tasks must not overlap,
  a source-compatible endpoint convention gives
  `(=> (and present_i present_j) (or (<= end_i start_j) (<= end_j start_i)))`.
- Within-job precedence and resource capacity are separate requirements. Do not
  impose precedence between unrelated jobs.
- Define ends from starts and durations exactly. Preserve alternative machine
  choices, calendars, optionality and zero-duration semantics.
- Discrete time-indexed capacity needs a source-supported finite horizon. For
  continuous time or an unstated horizon, do not guess a time grid; select an
  exact interval/event formulation whose preconditions hold.

Local degree constraints alone do not imply graph connectivity. Finite flow or
rooted reachability/rank encodings need a projection preserving precisely the
source-visible feasible set. Hidden constants can encode an outermost positive
existential, not one arbitrarily moved across negation or a universal quantifier.

Do not add symmetry breaking merely to reduce search: retaining one orbit
representative changes the full solution relation even if SAT/optimum survives.
Large encodings may be factored using exact repeated terms; never shrink domains
or omit rows to fit a budget.

These are mathematical patterns, not direct-SMT APIs called `all_different()` or
`cumulative()`. Native HIR CP constructors require selecting the separate HIR
route and consulting its live constructor catalog.
