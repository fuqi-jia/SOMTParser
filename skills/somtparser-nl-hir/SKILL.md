---
name: somtparser-nl-hir
description: Translate natural-language constraints directly into SMT-LIB, optionally use HIR for high-level constructors, repair candidates with compiler feedback, and export selected snapshots.
---

Use the installed SOMTParser Python package. Run the commands on the user's
chosen execution host; preserve repository instructions about remote testing.
`scripts/hir_bridge.py` calls the public API and performs no network requests.
The current agent supplies the model; a separate LLM service is optional.
This skill is the modeling workflow; the bridge executes validation and export.
Neither route requires MCP.

## Choose the proposal format

Prefer direct SMT-LIB for ordinary logical and arithmetic requirements. The
agent writes the formal program without first generating HIR JSON:

```sh
python scripts/hir_bridge.py request problem.txt --language smtlib2 > request.json
```

Return the request's formal-candidate JSON: `program` contains SMT-LIB text,
with the required `decision`, `assumptions`, `unresolved`, and source `links`.
Each link pairs an exact program substring with a half-open Unicode character
span in the original problem. Preserve mathematical domains, all constraints,
and the exact objective and direction. Keep unknown intent in `unresolved`.
Inline the instance data; do not emit file includes or solver options.

Use `--language hir` when the documented CP globals, finite folds, shaped
arrays, or required output contracts simplify an exact encoding. HIR provides
reusable constructors and lowering; it is optional for natural-language input.
Select one format for a candidate and keep it fixed during repair. The bridge
retains `hir` as its legacy default, so always pass the chosen language explicitly.

SMT-LIB validation uses the native frontend and shared compilation pipeline,
including its internal HIR. Direct proposal means that the **agent** need not
produce HIR; it does not mean the compiler bypasses its internal representation.
Parsing/type checking and decision/objective checks run before a direct SMT
candidate is reported valid. They do not solve the model or prove its intent.

## Construct an optional HIR candidate

Save the exact problem statement as UTF-8 text. Obtain the live request, schema,
and constructor catalog instead of recalling an older operator list:

```sh
python scripts/hir_bridge.py request problem.txt --language hir > request.json
```

The script path is relative to this skill directory. Optional `--context`
accepts a JSON file containing a string-to-string map of caller conventions;
HIR-only `--required-outputs` accepts a JSON file of name/sort/shape contracts.
Retain both unchanged throughout repair. Do not infer them from a benchmark's
reference answer.

Read `request.json` and generate a model JSON matching its schema. Use the
constructor catalog for arrays, finite folds, CP globals, soft constraints,
objectives and quantifiers. Preserve the source's domains, all constraints,
objective direction and exact coefficients. Cite half-open Unicode character
spans into the original text, not UTF-8 byte offsets. The provider model has
no `context` field; the caller attaches it.

Keep scalar literals scalar: an `Int` literal must be a JSON integer, not an
identifier or a JSON-encoded list/matrix string. Put source-provided tables in
`model.data` and use the HIR `data` lookup expression to index them. For
example, with `model.data = {"workers": [2, 3, 1]}`, use
`{"data":"workers","indices":[{"var":"i"}],"default":{"literal":0,"sort":"Int"}}`.
The lookup's `default` is required and applies outside the table; keep the
source-derived index guards when the model only defines in-range accesses.
For a matrix, provide one index per nested axis. Do not turn a table into a
scalar or infer a missing table or domain from a compiler error.

When the instance supplies indexed records (for example, task alternatives,
allowed tuples, graph arcs, or job operations), preserve every record and its
declared scope. Build expressions from the actual row indices and values; do
not extrapolate a repeated-looking pattern beyond the rows present in the
data. For scheduling, keep within-job precedence separate from resource
capacity: add precedence only between operations listed in the same job order,
and express shared-resource non-overlap as either valid ordering, gated by the
operations' selection decisions when operations are optional. If a task has
alternatives, encode the stated exactly-one or at-most-one rule explicitly;
do not activate every alternative by default.

Prefer compact constructors whose documented meaning matches the source, such
as `all_different`, `global_cardinality`, and `among`. Give auxiliary quantities
exact definitions when preserving the decision/cost relation requires equality.
Do not add symmetry restrictions or omit requirements to make a model smaller.

For routing and scheduling models, distinguish route position from entity
identity before writing time expressions. A route variable `x[i]` may mean the
city at position `i`, while `a[j]` may mean the arrival time at city `j`; these
are different index spaces. If the source relates them as `a[x[i]]`, preserve
that lookup instead of replacing it with a position-indexed `t[i]` unless the
source establishes that mapping. Preserve the stated route-vector length,
endpoint indices, loop ranges, and objective legs exactly. A route that returns
to a depot does not by itself require a time equality after the return leg; add
one only when the source states it. When a position-indexed representation is
used, define and check its mapping to all source-visible entity-indexed values
before claiming a complete relation comparison.

## Check and repair

```sh
python scripts/hir_bridge.py validate problem.txt model.json --language smtlib2 --out attempt-1
```

Use `--language hir` instead for an HIR proposal. Pass the same context/output-contract options used for the request. Inspect
`validation.json`, including JSON pointers and candidate-linked source excerpts.
Revise the complete model and validate into a new attempt directory. Keep prior
attempts. Stop when construction succeeds or the remaining uncertainty requires
source clarification; compilation feedback does not resolve genuine ambiguity.
Use an explicit retry budget for unattended API generation.

Compiler acceptance establishes that the candidate can be constructed. Check
source requirement coverage separately. Do not claim that schema/type checking
proves natural-language intent. During evaluation, keep reference models and
solver verdicts out of generation and repair prompts.

## Export the selected snapshot

```sh
python scripts/hir_bridge.py compile attempt-1/candidate.json \
    --digest SELECTED_DIGEST --out export-1
```

Read the digest from the validated candidate. It binds compilation to that exact
snapshot. When the user already authorized conversion, the agent may select the
candidate within that authorization; this API does not require another user
approval. Never remove unresolved alternatives merely to enable compilation.

The result contains `model.smt2` and `report.json`. Report construction, export,
whole-target loading, and semantic comparison as separate outcomes. Solver SAT
does not establish faithful translation or optimality. Preserve `unknown` and
failed checks as such.

For an application-managed provider, the direct route is
`propose_nl_with_repair(..., language="smtlib2", max_attempts=N)` followed by
`compile_candidate(..., accept_digest=candidate.digest)`. A future MCP adapter
can expose these same operations. Use `language="hir"` to select the constructor
route; the public library defaults remain unchanged.
