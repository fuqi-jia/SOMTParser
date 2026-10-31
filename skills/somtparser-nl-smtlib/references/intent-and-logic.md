# Intent, proof obligations and logic selection

Classify the semantic request, not isolated trigger words. “For all tasks” can
be a quantified constraint in a satisfiability problem; it does not necessarily
ask for a theorem. “At most” can be a hard bound rather than an objective.

| Intent | Faithful obligation |
|---|---|
| Feasibility / find assignment | Assert constraints and issue `check-sat` |
| Prove G under P | P and not G; UNSAT establishes the implication |
| Equivalence F and G | Search for a valuation satisfying their XOR/difference, with appropriate scope |
| Optimize | Keep hard constraints and original directed objective(s) |
| Preferences | Preserve hard/soft distinction, weights and grouping |
| Lower bound on minimum | Search for feasible cost below the proposed bound; UNSAT proves the lower bound |

A proof that the optimum equals k additionally needs attainability (or a precise
infimum claim). Asserting cost >= k and minimizing does not prove the original
lower bound: it removes the counterexamples. Do not label a candidate SAT model
as a proof. A universal claim's negation may introduce existential witnesses;
preserve quantifier scope and verdict polarity.

Lexicographic, Pareto and independent objectives differ. Explicit source priority
wins; a caller-authorized lex default can be recorded as an assumption. There
is no hidden default that replaces requested trade-offs. Unsupported priority
returns a machine-readable failure without asking the user.

Logic names are standardized combinations with restrictions, not arbitrary
concatenations of `A`, `UF`, `N`, `S`, `DT`. `QF_` excludes genuine quantifiers.
Division, casts, nonlinear terms, strings, datatypes and arrays all matter.
Do not treat every product containing a variable as nonlinear (constant times
variable is linear). Do not silently narrow an unrestricted domain to make QF.

This revision preserves the native emitter's logic, or reports null when absent.
It does not guess `QF_LIRA`/`ALL` from substring heuristics or blindly override a
known incompatible logic hint. A nullable logic is preferable to a false promise
that a narrower logic contains the formula. Solver dialect support is separate.

Reference: [SMT-LIB logic definitions](https://smt-lib.org/logics-all.shtml).
