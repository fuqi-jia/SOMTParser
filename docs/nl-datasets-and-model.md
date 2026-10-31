# Natural-language modeling through language configurations

Natural-language formalization is a core input path, not a proposed extension.
The implementation joins a proposal protocol to the existing language
configurations and translation constructions. An accepted formal model is still
an interpretation of the request: formal translation fidelity does not prove
that an LLM understood the request.

## Model and executable boundary

A modeling task is `(text, instance, context, decision, observables)`. Context
includes the numeric domain, finite or open universe, arithmetic conventions,
and any benchmark-specific task convention. Observables identify the entities
whose assignments and costs must be compared. These choices belong to the
model, rather than being inferred from the target solver's defaults.

The implemented path is:

```mermaid
flowchart LR
  N[Text and instance] --> C[Explicit language configuration and context]
  C --> P[Provider proposes formal model and source links]
  P --> V[Validate envelope and unresolved choices]
  V --> S[Select immutable candidate digest]
  S --> F[Existing language frontend]
  F --> R[Typed relational core and translation contract]
  R --> T[SMT or OMT]
  T --> E[Decision and dataset witness checks]
```

`propose_nl(..., language=..., context=..., provider=...)` implements four
closed-input configurations: `minizinc`, `lp`, `xcsp3`, and `smtlib2`. The
original `typed` configuration remains available, including the deterministic
English/Chinese grammar. Language selection is explicit; an automatic router
has not been evaluated. The model may use the selected frontend's accepted
constructs, including CP constraints that the small typed JSON grammar cannot
express. The formal schema is available as
`somtparser._nl_formal.formal_schema(language)`.

The candidate binds the text, context, language, formal program, assumptions,
unresolved issues, source links, provider and execution metadata to its digest.
Context cannot be overwritten by the provider. Source links check character
boundaries and literal formal fragments; they do not prove semantic coverage.
Compilation checks the stated decision against the actual objective count.
Unresolved interpretations cannot compile. Include files and XML external
declarations are excluded from generated inline inputs. Generated Python is
never a supported formal candidate language. A dataset's trusted Python
reference exporter is a separate, explicitly audited reference-side step.

The report keeps intent preservation `not-proved`. SAT establishes neither
optimality nor correctness of the modeled requirement. A scalar observable
projection is available for the typed configuration; formal-language candidates
require a dataset-specific witness checker and refuse the generic projection
API. MiniZinc generator folds are supported, e.g. `sum(i in 0..6)(x[i])`,
and since 2026-09-19 so are the stdlib's whole-array aggregations
(`sum(x)`, `product(x)`, `forall(x)`, `exists(x)`), folded over the array's
declared index set.

```python
from somtparser import propose_nl, compile_candidate
from somtparser.deepseek import DeepSeekProvider

c = propose_nl(text, language="lp", context={
    "numeric_domain": "Nonnegative continuous Real decision variables",
    "decision": "Single-objective linear optimization",
}, provider=DeepSeekProvider())  # DEEPSEEK_API_KEY, never committed
# Inspect c.model and c.diagnostics. Selection refers to this exact snapshot.
t = compile_candidate(c, accept_digest=c.digest)
if t.ok:
    print(t.to_smt2())
```

The CLI supports `somt-nl propose request.txt --provider deepseek --language lp
--context context.json`. A benchmark may select a candidate automatically as an
experimental policy; that is not human intent validation.

## Packaged dataset adapters

`somtparser.nl_datasets` exposes strict reference-data adapters as library APIs.
NL4Opt coefficients use exact `Fraction` arithmetic and positive denominator
clearing; the returned objective scale is explicit. Corrections are identified
by full record hashes in the packaged correction ledger. Unknown aliases,
unsupported units and missing objectives are rejected rather than guessed.

IndusCP helpers discover caller-provided task trees, read statements and expected
objective metadata, and normalize only recognized singleton-count XCSP3 exports.
The external PyCSP3 exporter and datasets are supplied separately by the caller.
Dataset content and its license obligations do not become part of the parser
package merely because an adapter can read it.

`somtparser.folio` parses supported first-order annotations over a nonempty,
unbounded universe. For entailment, check premise consistency, then check both
`premises and not conclusion` and `premises and conclusion`. Their conclusive
answers distinguish entailed, contradicted and undetermined; inconsistent
premises and solver unknown remain separate outcomes.

## Semantic validation

Under an explicit observable mapping, feasible-relation equivalence requires
`F xor G` to be unsatisfiable. Compare objective maps separately and preserve
objective order and direction. Parser acceptance, one satisfying solution and
SAT/UNSAT agreement alone do not establish equivalence or natural-language
intent preservation. Unknown, timeout and unsupported input are not passes.

The package provides adapters and modeling APIs. Corpus downloads, experiment
schedulers, model-comparison campaigns and their recorded results are separate
research workflows and are not shipped in this library repository.
