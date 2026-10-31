# Comparing candidate routes

The skill supports HIR, direct SMT and hybrid candidates. Use the same source
text and caller context when comparing their interpretations. Each route has
its own schema; preserve the complete candidate instead of truncating it to
match another route.

Keep construction validation separate from solver loading, solving and semantic
comparison. Construction feedback can repair syntax or API use; it does not
establish that the candidate captures the intended problem. Reference answers
and semantic counterexamples must not be silently inserted into the source.

When a reference interpretation is available, compare complete feasible
relations and ordered objective maps after explicitly mapping observables and
projecting private auxiliary variables. Preserve unknown, resource exhaustion
and unsupported cases as inconclusive results.

The ordinary skill regressions use hand-authored fixtures and a complete
relation/objective oracle in `test/python/_skill_relation_oracle.py`. They test
API behavior and selected encodings; they are not measurements of model
accuracy on an external dataset.

The bundle builder excludes this developer guide from generation bundles.
Production use translates the selected candidate; optional developer checks
are described in [validation](validation.md).
