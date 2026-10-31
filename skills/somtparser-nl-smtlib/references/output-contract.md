# Noninteractive translation interface

Production translation never calls a solver, asks the user, or interprets a
solver model. The calling agent converts natural language into one of the three
candidate representations and supplies it to `scripts/ir2smt.py`.

Parameters: `--source file` (required), `--route hir|smtlib2|hybrid` (default hir),
`--dialect z3|optimathsat|smtlib-pure` (default z3),
`--context file` (optional string-to-string conventions),
`--mode full|code|ir` (default full). `--request` obtains the route's live input
contract without generating, translating or solving a model.

Full output is a single JSON object with fields:

```json
{
  "status": "translated",
  "ir": {},
  "code": "SMT-LIB / OMT text",
  "assumptions": [],
  "ambiguities": [],
  "diagnostics": [],
  "meta": {
    "route": "hir", "dialect": "z3", "logic": null,
    "task": "optimization", "objectives": 1, "soft": 0,
    "solver_executed": false, "intent_preservation": "not-proved",
    "degraded": false
  }
}
```

Hashes identify source, IR, selected candidate and code. `verdict_polarity` is
`invert` for a validity counterexample query and `preserve` otherwise. No expected
SAT answer is invented. `objectives` counts emitted minimize/maximize commands;
`soft` separately counts assert-soft commands. A solver may normalize grouped
soft constraints into additional objectives. `mode=code` emits raw SMT text
without fences; `mode=ir` emits JSON.
JSON avoids delimiter collisions and YAML's implicit numeric/type conversions.
Human-readable Markdown sections may be rendered by a caller, not parsed as the
canonical wire format.

Failures have `status=translation-error`, `code=null`, diagnostic messages and a
nonzero exit. In code mode errors go to stderr, leaving stdout free of malformed
SMT. No unsupported optimization silently becomes satisfiability.

Noninteractive does not mean guessing anything: caller-authorized defaults may
be adopted and recorded in assumptions. There is no automatic time bound,
integrality or lexicographic policy without a source/context basis. A genuine
remaining ambiguity returns a structured failure without asking a question.
Do not fabricate a calibrated confidence score from counts of assumptions.

Determinism applies to fixed candidate + runtime + options. An LLM's interpretation
is not guaranteed deterministic merely because its temperature is zero. Record
model/version/settings and retain exact candidates in experiments.
