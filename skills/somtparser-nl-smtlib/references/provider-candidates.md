# Candidate generation for an API model

The user message fixes the route and provides its current JSON schema. Return
**only that candidate**, not the generator's final `status/ir/code/meta` response.
You are writing the input to a deterministic compiler, not running the compiler.
No filesystem access or solver tools are implied by this prompt.

Use exact source quotes for spans; the compiler calculates Unicode offsets.
A repeated quote needs `occurrence` (zero-based). Do not add span fields to
declarations. Unknown values to solve for or several feasible assignments are
not ambiguous interpretation; keep `unresolved: []` in those cases.

## HIR candidate

Always include all required root fields, even empty `functions`, `objectives`
and `constraints`, and `goal: null` when no proof goal exists. For example, the
source `An integer u is at least 2. Minimize u plus 3.` can be represented as:

```json
{"schema":"somt-hir-model-v1","language":"hir","decision":"optimization",
 "declarations":[{"name":"u","sort":"Int","lower":2}],
 "functions":[],"constraints":[],
 "objectives":[{"sense":"minimize","expr":{"op":"add","args":[{"var":"u"},{"literal":3,"sort":"Int"}]},"span":{"quote":"Minimize u plus 3."}}],
 "objective_order":"single","goal":null,"assumptions":[],"unresolved":[]}
```

`{"var":"u"}` is a complete expression. **There is no `op:"var"`.**
`{"literal":3,"sort":"Int"}` is a constant; `{"op":"ge","args":[...]}`
is a Boolean relation. Every constraint's `expr` must be Boolean. A variable
alone is not a constraint when its sort is Int/Real. Declaration bounds already
assert their domain; do not add a fake constraint just to fill an empty list.
Follow the live schema for all other constructors and their exact fields.
Declarations have `name`, `sort`, and optional bounds/shape; they do not have a
`span` field. Spans belong to constraints, objectives, soft constraints and goals.
For a source-required nonnegative Real variable use
`{"name":"x","sort":"Real","lower":"0"}`. Even integral Real bounds
are exact strings, not JSON integers. A Real expression literal is
`{"literal":"1/3","sort":"Real"}`; an Int literal uses a JSON integer.
Do not add a nonnegative bound merely because this syntax example has one.

## Direct SMT candidate

For the same illustrative source:

```json
{"schema":"somt-nl-formal-v1","language":"smtlib2","decision":"optimization",
 "program":"(declare-const u Int)\n(assert (>= u 2))\n(minimize (+ u 3))\n(check-sat)",
 "assumptions":[],"unresolved":[],
 "links":[{"span":{"quote":"An integer u is at least 2."},"fragment":"(assert (>= u 2))"},
          {"span":{"quote":"Minimize u plus 3."},"fragment":"(minimize (+ u 3))"}]}
```

Do not emit `set-option`, includes or solver execution commands beyond the final
query. Compiler-owned configuration belongs to the exporter. Each `fragment`
is a literal substring of **the final program you return**, not a quotation
from the source or a deleted prior command. After changing the program, update
its links too. Source spans must fit the unchanged source's Unicode length.

## Hybrid candidate

Here is the same illustrative source with its lower-bound relation supplied by
SMT and its objective owned by HIR:

```json
{"schema":"somt-nl-hybrid-v1",
 "hir":{"schema":"somt-hir-model-v1","language":"hir","decision":"optimization",
        "declarations":[{"name":"u","sort":"Int"}],"functions":[],"constraints":[],
        "objectives":[{"sense":"minimize","expr":{"op":"add","args":[{"var":"u"},{"literal":3,"sort":"Int"}]},"span":{"quote":"Minimize u plus 3."}}],
        "objective_order":"single","goal":null,"assumptions":[],"unresolved":[]},
 "smt_constraints":[{"span":{"quote":"An integer u is at least 2."},"term":"(>= u 2)"}]}
```

The term is `(>= u 2)`, **not** `(assert (>= u 2))`. The objective occurs
only in `hir.objectives`; `(minimize ...)` is never an SMT constraint term.
HIR owns every declaration, explicit declaration bound and objective. SMT terms
refer to the same declared names and add hard constraints. No SMT declarations,
options, query commands or objectives can occur inside a term. Empty extensions
are legal when HIR represents the complete source; never invent an extra clause
merely to make a hybrid example nonempty. The schema's root definitions resolve
references used by the nested HIR model. HIR macros can be used in its HIR field.

## Construction repair

The `repair` object, when present, contains your previous candidate and actual
construction diagnostics. Return a complete corrected candidate. Keep all
source constraints and objectives. Correct missing fields and incorrect term
shapes; do not remove requirements to make type checking pass. These diagnostics
say nothing about whether the source interpretation is right. Unresolved source
ambiguity remains visible; unsupported syntax or unknown values to solve for
are not automatically source ambiguity.
