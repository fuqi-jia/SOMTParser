# Weighted preferences in JSON HIR

An optional `soft_constraints` array in `somt-hir-model-v1` lets a natural-language
provider or another JSON producer construct weighted preferences directly:

```json
{
  "schema": "somt-hir-model-v1",
  "language": "hir",
  "decision": "optimization",
  "declarations": [{"name": "p", "sort": "Bool"}],
  "functions": [],
  "constraints": [],
  "soft_constraints": [
    {"expr": {"var": "p"}, "weight": "7", "group": "", "span": [0, 9]}
  ],
  "objectives": [],
  "objective_order": "single",
  "goal": null,
  "assumptions": [],
  "unresolved": []
}
```

For the source `Prefer p.`, `build_hir(model, "Prefer p.")` constructs one
preference whose violation costs 7. Hard requirements remain in `constraints`.
Each soft item requires all four fields. Its expression must be Boolean; CP
constructors and source-defined functions may be used inside it. The span is a
nonempty half-open interval of source Unicode code points. The native extension
must provide `HirModel.soft_constrain`.

Weights are positive ASCII integer **strings** of arbitrary precision. They
never pass through a machine integer or floating point value. Zero, negative,
fractional and scientific-notation weights are not accepted by this API.
Leading zeroes are retained in the candidate snapshot and canonicalized only
when constructing the native weight.

One item contributes its weight once when its entire formula is false. Repeated
items contribute independently. A preferred conjunction is not split into
separately charged conjuncts. Within each group, violation costs are added.
The empty group string denotes the default group; other values must be valid
SMT symbol spellings. `cost` and `|cost|` name the same group.

Group costs occur in order of first appearance, followed by explicit objectives
in their list order. Set `objective_order` to `lexicographic` when there is more
than one effective objective; use `single` for one. This ordering must reflect
the source requirement. The JSON representation does not encode arbitrary
interleaving of soft groups and arithmetic objectives.

The constructor catalog and provider prompt expose this contract. CP expansion
and expression normalization retain weights, groups, list order, repetitions
and spans. Saved NL candidates bind all these fields into their digest, and
translation reports include the soft source links. A successful construction
checks the selected formal model; it does not prove that a provider interpreted
the natural-language requirement correctly.

`HirBuilder.soft_constrain(expr, weight, group="", source_path="")` provides the
same operation for incremental JSON expression construction. Z3 output uses
`assert-soft`; target dialects that cannot preserve the soft objective contract
must report that limitation instead of dropping preferences.
