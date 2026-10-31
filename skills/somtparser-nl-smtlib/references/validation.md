# Validation layers

| Evidence | Executable path | Established property |
|---|---|---|
| Request | `smt_bridge.py request` | Exact source, live schema and context |
| Construction | `smt_bridge.py validate` | Candidate checks accept this snapshot |
| Export | `smt_bridge.py compile` | Installed SOMTParser exports the selected interpretation |
| Full load | `smt_bridge.py check` | Z3 loads emitted assertions and objectives |
| Candidate solve | `smt_bridge.py check --solve` | Verdict for that formula with available model/objective data |
| Reference comparison | Independent source-specific checker | The recorded relation, objective or label metric |

The bridge logs hashes, version and resource limits. Timeout, resource kill,
unknown and load failure never become passes. Objective bounds are raw Z3
evidence; printed model values do not alone establish optimality or attainability.
`Optimize.objectives()` normalizes maximization, so preserve source/export
direction when reporting actual objective values.

Ordinary developer regressions use independent semantic helpers under
`tools/semantic_checks/` and hand-authored skill cases in
`test/python/_skill_relation_oracle.py`. The packaged FOLIO adapter provides
premise consistency and three-way label checks. Dataset-wide experiment
schedulers and archived results are maintained separately from this library.

Full equivalence requires correct observable mappings and projection when
auxiliaries differ. For independent-solver fallback, record the weaker evidence:

1. SAT: obtain complete source and target solutions, map observables in both
   directions and test each against the other full model. Partial bindings with
   existential completion are not complete witness cross-checks. Arrays and
   functions require their relevant complete interpretations.
2. Optimization: also evaluate original objectives exactly on both assignments.
   Distinguish best-known from proven-optimal. A no-better-solution query retains
   all original constraints and leaves decisions unfixed; fixing the candidate
   would invalidate this optimality check.
3. Independent UNSAT: record both inputs, versions and results as agreement,
   separately from a formula-equivalence proof.

The generic bridge does not supply arbitrary source-solver/mapping adapters for
witness or optimality comparison. Use the dataset's actual adapter and name the
path run. Never infer natural-language intent preservation from parser success,
one solution, or SAT/UNSAT agreement alone.
