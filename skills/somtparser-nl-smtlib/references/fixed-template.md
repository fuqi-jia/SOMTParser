# Deterministic generation

The installed native emitter owns declarations, domain constraints, expression
lowering and OMT rendering. The skill generator reuses it; it does not ask an LLM
to repeatedly reconstruct those mechanisms from a prose template.

Final script structure:

```smt2
; SOMTParser translation | route=<route> | dialect=<dialect>
<native configuration, declarations, definitions, hard constraints>
<native soft-constraint/objective encoding, preserving order>
; query
(check-sat)
```

The generator canonicalizes S-expression whitespace while respecting quoted
symbols/strings. It preserves backend command order; sorting objective groups or
moving definitions to satisfy decorative headings could change semantics.
There is exactly one final query. Hybrid assertions are added before that query
and the whole composition is re-parsed and exported.

Do not unconditionally append `get-model` and `get-unsat-core` to the same script:
their validity depends on the result and enabled features. The caller issues
result-dependent commands after observing SAT/UNSAT. Similarly, one Pareto query
does not enumerate a full frontier. Translation does not perform an enumeration.

If the native package is unavailable, an agent may use the direct-SMT guidelines
to produce a clearly labeled unvalidated draft. It must not claim generator
determinism, successful compilation or a translated API result without running
the non-solver generation checks. Evaluation does not mix such drafts with
successfully generated artifacts.

The direct candidate is one model, not an incremental solver transcript.
`push`, `pop`, resets, `check-sat-assuming`, multiple queries, and construction
after a query are rejected so normalization cannot erase their semantics.
Omit `exit`: the calling agent owns the solver session.
