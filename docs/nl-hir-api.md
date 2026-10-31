# Direct natural-language to native HIR

`propose_nl(source, language="hir", context=context, provider=provider)` requests
`somt-hir-model-v1`. The provider receives `hir_schema()` and its constructor
catalog `hir_api()`. `compile_candidate(candidate, accept_digest=candidate.digest)`
constructs immutable C++ HIR expressions directly, then invokes the existing
HIR type checker, encoding passes, semantic contract checks, and OMT emitter.
There is no intermediate SMT input script or generated Python execution.
The original typed and textual language routes remain separate baselines.

`hir_schema()` describes recursive expression constructors, their allowed fields,
and the operator catalog's arities. For example, a function application uses
`apply` and `args`; a finite-array read uses `at` and `indices`. Unknown `call`
nodes and three-argument `select` nodes fail structural validation. Folds,
quantifiers, function bodies, and CP constructors use the same recursive schema.
`build_hir()` still checks names, types, dimensions, source spans, definedness,
and other conditions that depend on the surrounding model. It invokes the shared
C++ HIR type checker before returning, without lowering or invoking a solver.
Type errors include the containing JSON expression path; common operand errors
identify the offending argument. Neither structural
validation nor successful construction proves agreement with natural language.

Declaration bounds apply only to `Int` or `Real` elements, including shaped
arrays. Omit numeric bounds on `Bool`; use `ite(choice, 1, 0)` when counting
Boolean choices. Integer bounds must be exact integers and real bounds exact
decimal/rational strings. Contradictory numeric bounds are valid models with an
empty feasible domain, so validation does not reject them.

Every HIR model must include the complete top-level schema, including fields
that are empty or null for a particular decision type. The required keys are
`schema`, `language`, `decision`, `declarations`, `functions`, `constraints`,
`objectives`, `objective_order`, `goal`, `assumptions`, and `unresolved`.
`schema` is exactly `somt-hir-model-v1`, `language` is exactly `hir`, and the
four collections `declarations`, `functions`, `constraints`, and `objectives`
are arrays. `assumptions` and `unresolved` are arrays of strings; use `[]`
when none are supplied. `objective_order` is required even when there are no
objectives and must be `single` or `lexicographic`. Use `single` for the usual
single objective, including satisfiability models with no objective. Do not
add an objective just to populate this field. `goal` is required and is null
for satisfiability and optimization; validity models provide a goal and no
objectives. `decision` is `satisfiability`, `optimization`, or `validity`,
consistent with the objective and goal fields.

The optional `interpretation_notes` array contains strings explaining the already
encoded interpretation. These notes are preserved in the immutable candidate and
translation report, and covered by its digest, but add no constraints. Use
`assumptions` for explicitly applied modeling conventions and `unresolved` for
competing readings that still need resolution. Neither notes nor assumptions
automatically resolve an `unresolved` entry; such candidates remain refused.
A source requirement must still appear in the model, even if described in a note.

A minimal satisfiability model therefore has this shape (add the source-grounded
declarations, constraints, assumptions, and unresolved entries as needed):

```json
{
  "schema": "somt-hir-model-v1",
  "language": "hir",
  "decision": "satisfiability",
  "declarations": [],
  "functions": [],
  "constraints": [],
  "objectives": [],
  "objective_order": "single",
  "goal": null,
  "assumptions": [],
  "unresolved": []
}
```

For offline generation batches, `tools/nl_hir_batch.py prepare` attaches the
complete live schema and operator catalog to every source/context request:

```sh
python tools/nl_hir_batch.py prepare --source-package sources.json --destination requests
python tools/nl_hir_batch.py seal --requests requests/requests.json --outputs responses --destination sealed
```

The source package contains a `cases` array of objects with `id`, `source`, and
optional string-valued `context`. Save each response as `responses/0.json`,
`responses/1.json`, and so on, containing exactly `id`, `model`, and
`modeling_notes`. The model omits caller-owned context. Sealing checks the
source hash, live API consistency, response envelope, and public `build_hir()`
construction for every response before writing any seal. It preserves the
candidate models and records request/output hashes. A construction-valid seal
does not establish successful translation or equivalence to a reference model;
those require the separate translation and semantic checks.

For provider-generated candidates, custom sorts use objects such as
`{"Uninterpreted":"Entity"}` in declarations, function signatures, and
quantifier binders. A native quantifier has the separate
`{"quantifier":"forall|exists","binders":[...],"body":...}` shape;
`forall` and `exists` are not operator names. JSON Int literals are integers,
Bool literals are JSON booleans, and exact Real literals are strings. If the
task context names an observable, the model must declare and constrain it as
specified there. Put an issue in `unresolved` only when competing readings of
the source change the model and context does not settle the choice. Missing
background facts, unstated types, and names can be represented with declared
uninterpreted individuals and predicates while asserting only stated facts.
The candidate review guide explains source coverage,
representation choices, finite-array boundaries and separate evaluation claims.

The API exposes Bool, mathematical Int, exact Real, total arrays, uninterpreted
sorts, machine-width bit-vectors (`{"BitVec": width}`), IEEE floating point
(`{"FloatingPoint": [eb, sb]}`), character strings (`"String"`), scalar
declarations with explicit bounds, declared and defined functions/predicates,
Boolean/arithmetic operations, if-then-else, array select/store, all-different,
Boolean counts, finite sum/forall/exists folds, native open-domain quantifiers,
and single or explicitly lexicographic objectives. The non-indexed bit-vector,
floating-point and string operators are ordinary entries of the operations
table; floating-point arithmetic takes a rounding mode through the `{"rm":
"RNE|RNA|RTP|RTN|RTZ"}` literal constructor. The indexed operators —
`extract`, `zero_extend`/`sign_extend`, `rotate_left`/`rotate_right`,
`repeat`, `int2bv`, `divisible`, `to_fp`/`to_fp_unsigned`, the bit-pattern
reinterpretation `ieee_bv_to_fp`, and `fp.to_sbv`/`fp.to_ubv` — take their
indices in a dedicated `{"op_indexed": {"op", "indices", "args"}}`
constructor; index counts and non-negativity are validated by the API, and
width relations between indices and operand sorts are checked by complete native
HIR validation. Optional declaration shapes
provide zero-based multidimensional arrays and per-element bounds. An empty shape `[]` adds zero axes and is equivalent to omitting shape; `[0]` still denotes an empty array. The declared sort and scalar bounds are preserved for zero axes. Data lookup
constructors accept nested exact tables with an explicitly supplied out-of-range
default; that default is part of the model, not inferred by the compiler. Unrestricted quantifiers
are never replaced with a finite enumeration. Finite ranges are half-open.
Division conventions are explicit. A denominator may be a nonzero numeric
literal or a numeric variable that a local comparison guard proves nonzero.
The guard may enclose an implication consequent or an `ite` branch, or occur
in the same conjunction/disjunction. For example, `d >= 2 -> p mod d != 0`
can express primality without an arbitrary finite divisor bound. Facts retain
the exact lexical binding and cannot cross a shadowing quantifier or fold.
This adds no global `d != 0` constraint: assignments where the guarded branch
is irrelevant remain possible. Unguarded or otherwise unproved symbolic
denominators still require an explicit source interpretation before support.
The guarded-division validation note
distinguishes API acceptance from generated-model semantic correctness.

Finite numeric sums can share a generated function when their typed expression
templates match. Variable, array and literal arguments remain explicit; sharing
keys preserve argument positions, sorts, array shapes and fixed table contents.
Generated functions are auxiliary and do not become public observables. Nested
binders and partial division/modulo retain the existing construction path. The
100,000-node construction limit still applies, including helper construction.
The sum-sharing qualification
records independent solver checks and the full Python suite. This compiler
optimization does not establish improved natural-language generation accuracy.

The public `HirBuilder` offers `declare`, `declare_function`, `define_function`,
`expr`, `constrain`, `validate` and `translate`; `builder.model.objective` consumes a constructed HIR expression.
`validate()` raises `ModelError` on a native type error and otherwise returns
diagnostics. It does not establish satisfiability or natural-language fidelity.
The `eq` operator accepts two or more compatible operands and requires all of
them to have the same value. Its negation means that at least two differ;
`distinct` instead requires every pair to differ. The constructor catalog
advertises this arity to natural-language providers, and native HIR preserves
the chain directly through SMT lowering.
Exact function definitions add typed `binders`, `body`, and a nonempty source
`span` to a declared signature. They support forward references and lexical
shadowing; native validation rejects cycles. The
[function-definition guide](nl-hir-defined-functions.md) gives the JSON shape
and current body restrictions.
For example:

```python
from somtparser import HirBuilder
b = HirBuilder()
b.declare("x", "Int", lower=0, upper=10)
b.constrain({"op": "ge", "args": [
    {"var": "x"}, {"literal": 3, "sort": "Int"}
]})
b.model.objective(True, b.expr({"var": "x"}))  # maximize
result = b.translate()
assert result.ok
print(result.to_smt2())
```

Candidate construction errors include the original JSON expression path, such
as `constraints[20].expr.body.args[0].args[5].args[1]`. Providers can use that
location to correct a subsequent proposal. Each operand is an expression
object: an Int constant is `{"literal": 5, "sort": "Int"}`, while a variable is
`{"var": "x"}` directly, never inside `literal`. Numeric comparisons require
numeric operands; an `ite` condition must be Bool. `le`, `lt`, `ge`, and `gt`
accept 2 to 10,000 numeric operands and relate adjacent operands. For example,
`{"op":"le","args":[{"literal":0,"sort":"Int"},{"var":"x"},{"literal":10,"sort":"Int"}]}`
means `0 <= x` and `x <= 10`. Negating the chain negates that whole conjunction. The compiler reports these
errors without rewriting the candidate or issuing a provider request. Improved
diagnostics alone do not count as improved generation accuracy.

`propose_nl_with_repair(source, provider=provider, language="hir",
context=context, max_attempts=3)` explicitly enables bounded feedback. It returns
a `ProposalTrace` with immutable `attempts`, the final `candidate`, and a
`stop_reason`. The first request is the ordinary proposal request. Subsequent
requests carry a `repair` object with the previous model in provider response
form (caller-owned `context` remains outside it), digest, diagnostic
paths/messages, and instructions to preserve the source requirements. Source,
schema, and caller context stay fixed. The DeepSeek adapter forwards this
feedback; each attempt is a separate provider request. The default is one
attempt, successful validation stops the loop, and service exceptions propagate
without retrying. All tests of this API use offline providers.

The trace retains unsuccessful candidates as well as the final proposal. A
valid candidate still requires `compile_candidate(candidate,
accept_digest=candidate.digest)` and does not establish natural-language
accuracy. Evaluation must report first-attempt and repaired accuracy separately;
this interface neither consumes a reference answer nor measures that accuracy.

Candidate constraints, objectives and validity goals carry half-open Unicode
source spans. Context is attached by the caller and covered by the immutable
candidate digest. A source span establishes location, not semantic coverage.
Unresolved candidates cannot compile. The native translation contract begins
at the selected HIR model: natural-language intent preservation remains
`not-proved`. Tests use independent solver formulas, including open-domain
countermodels, exact fractions, finite arrays and objective values.

Bit-vector literals are `#b…`/`#x…` text whose width must equal the declared
sort width; string literals are plain JSON strings; floating-point literals are
decimal strings, the five special values (`+oo`, `-oo`, `+zero`, `-zero`,
`NaN`), or `["#bS", "#bE", "#bM"]` bit triples with 1, eb and sb-1 bits.
Bit-vectors are machine-width: arithmetic wraps modulo 2^width, and signed and
unsigned orderings and divisions are distinct operators. Floating point is
IEEE 754 per SMT-LIB; `fp.eq` is IEEE equality, under which NaN equals
nothing, and is distinct from structural `=`. Strings are SMT-LIB sequences of
characters with integer indices; out-of-range `str.at`/`str.substr` yield the
empty string and `str.indexof` yields -1.

Finite `model.data` tables must be rectangular with one scalar leaf sort.
Every lookup index must have sort Int, its index count must match the table
rank, and its explicit default must match the leaf sort when the table has
leaves. An empty list declares one known empty dimension; deeper dimensions
cannot be inferred from absent rows. Empty tables still validate index sorts
and rank rather than bypassing type checks.

Symbolic data lookups share immutable constant-array values. Each source axis
has its own bounds check, so an out-of-range column cannot alias the next row.
Literal indices specialize a table only after its entire shape and leaf sorts
have been checked. The cache keys exact contents, so later edits to the public
`builder.data` dictionary cannot silently reuse an earlier value. Defaults are
compiled at each use and retain local quantifier bindings. A general constant
array is also expressible as
`{"const_array":{"index_sort":"Int","value":{"literal":0,"sort":"Int"}}}`;
its element sort comes from the value, which may depend on a bound variable.

Algebraic datatypes use the model-level `datatypes` field, or the builder's
`declare_datatypes` method. Constructor, selector and tester expressions appear
in `hir_api()`; result datatype instances and selector result sorts are explicit.
Inductive declarations are checked for finite inhabitants, including through
parameterized mutual recursion. Array domain and valid index constraints are
explicit. A successful compile does not
establish NL correctness, reference agreement, satisfiability or optimality;
the new theories change what a model can say, not what compiling one proves.

Z3 export represents supported `Set Int` terms as Boolean arrays. Cardinality
uses exact finite support from set constructors or unconditional interval
constraints. A dynamic array-of-sets lookup can use those constraints only when
every possible indexed cell has a proved finite carrier. Lexical shadowing and
separate assertion contexts cannot share proofs. Other set element types,
unbounded quantified carriers, and input-relative universe/complement retain
the native Set dialect; requesting the unsupported Z3 encoding raises an error.
`Formula(..., backend="z3").solve()` uses the same exporter and records
`z3-finite-set-arrays` in a returned result. Export success is separate from
type validation and from a solver's ability to decide the resulting formula.


## CP constructor API

The standard `hir_api()` catalog includes the versioned `cp_constructors`
catalog from `somtparser.hir_cp.cp_api()`. `HirBuilder.expr()` and
`build_hir()` accept these expressions directly and construct native HIR before
type checking, retaining supported global constraints until lowering.
Natural-language HIR proposals
use that same standard path; the accepted candidate snapshot retains the
provider's CP expression and is not rewritten during compilation.
`expand_cp_model()` produces the explicit expanded JSON model;
`build_cp_hir()` uses the standard direct HIR path. `CpProvider(provider)` remains an optional
wrapper for providers that benefit from receiving a separate CP catalog in
their context. It keeps the returned constructors compact until native HIR
construction. In particular, minimum/maximum and element do not pass through
eager JSON expansion; repeated operand trees can otherwise dominate model size.

The constructors expand to the existing native HIR model without emitting an
intermediate formal-language program:

- vector sum, minimum, maximum and absolute value;
- all-different (including zero-ignoring distinctness), Int among-set counts,
  Boolean cardinality (`count_true` and `at_most_one`),
  global cardinality, positive/negative tables, lexicographic
  order and total element lookup;
- exact undirected/directed subgraph connectivity (`connected` and `dconnected`);
- non-overlap with constant nonnegative durations, cumulative scheduling with nonnegative Int-expression durations/demands, and multidimensional `diffn`;
- a single Hamiltonian circuit, a subcircuit with explicitly optional empty
  selection, and finite-state regular-language membership.

For example, a constraint expression can be
`{"cp":"all_different","items":{"array":"x","length":5}}`.

`circuit` visits every vertex. For a route that may skip vertices, use
`{"cp":"subcircuit","successors":{"array":"s","length":5},"allow_empty":false}`.
Successor indices are zero-based; `s[i] = i` means vertex `i` is inactive.
All active vertices must belong to one nontrivial cycle, so multiple disjoint
tours are rejected. Set `allow_empty` explicitly from the source: `true`
permits the all-inactive assignment (and an empty vector), while `false`
requires a nontrivial tour. The encoding uses locally existential anchor and
rank variables, preserving the constructor's meaning under negation and
implication. This differs from allowing an arbitrary union of cycles.

The ordinary `{"op":"all_different","args":[{"var":"x"}]}` form also accepts
an Int array declared with an explicit `shape`. It compares all in-shape cells
in row-major order, including when mixed with scalar arguments. It does not
infer an extent for a total SMT Array declaration. A locally bound variable
shadows the global declaration and is never expanded using that declaration's
shape. Empty shaped Int arrays contribute no cells; empty non-Int arrays
still fail the element-sort check. Total expansion is limited to 10,000 cells.
The builder assigns fresh internal names to quantified binders while retaining
their lexical source bindings, so nested and global-name shadowing is supported
without violating native HIR's requirement for distinct binder names.
The `all_different_except_0` constructor accepts exact Int terms and ignores
any number of zeros while requiring every nonzero value to be distinct. Its
indexed form is `{"op":"all_different_except_0","args":[{"var":"x"},
{"literal":0,"sort":"Int"},{"literal":5,"sort":"Int"}]}` and covers the
half-open index range `[0, 5)`. A whole declared finite Int array may also be
passed as a single argument and is expanded over its declared shape. Empty
lists and empty ranges are true; every list operand is still checked for exact
Int sort before that identity is applied.
The CP constructors `connected` and `dconnected` take fixed zero-based endpoint
vectors `from` and `to`, a Bool `nodes` vector and a Bool `edges` vector. Their
lengths must agree (`from` and `to` have one entry per edge); endpoints must
refer to a node position. A selected edge requires both endpoint nodes to be
selected. Both relations require a nonempty selected node set and a selected
root that reaches every selected node; `connected` can traverse an edge either
way, while `dconnected` follows only `from` to `to`. The HIR builder keeps the
connectivity witness inside the Boolean relation, so negation applies to the
whole global. MiniZinc frontends normalize source index ranges to these
zero-based positions after checking their original index sets.
Use the machine-readable catalog for the complete field contracts. Source spans,
objectives, domains and unresolved interpretations remain mandatory as in base HIR.
`among` returns the number of items in an explicit finite Int set; repeated
entries in its `values` list denote one set member. `count_true` accepts a vector
of exact Bool expressions and returns an Int count, counting each vector
position independently even when the same expression occurs more than once.
`at_most_one` accepts the same Bool vector and returns a Bool relation that is
true exactly when no more than one position is true. Both Boolean constructors
use a linear-size count representation, so `at_most_one` avoids generating all
pairwise exclusions. Empty vectors have `count_true = 0` and
`at_most_one = true`. Bool constructors reject Int and Real expressions without
coercion; they do not deduplicate repeated positions. Vectors may be explicit
expression lists or the standard shaped-array vector descriptor.
`global_cardinality` takes
distinct `values`, parallel Int-expression `counts`, and a required Boolean
`closed`; `closed=true` also constrains every item to one of those values.
Operands must have exact Int sort, with no Real or Bool widening. Expansion
uses the logically true `mod_euclid(term, 1) = 0` as a type-checking guard, so
the requirement survives nested and legacy JSON expansion paths. No implicit
domain is inferred, and both macros preserve ordinary expression polarity and
quantifier scope.
`CpProvider(DeepSeekProvider(...))` explicitly supplies this catalog and retains
`last_cp_model` as a separate snapshot of the raw response. Save that snapshot
and the accepted candidate for reproduction. Call `expand_cp_model()` explicitly
only when an expanded JSON representation is needed. This is a distinct generation configuration, not a retroactive
change to an existing experiment.

Array-vector lengths are explicit, element lookup requires an out-of-range default,
and intervals are half-open. Zero-duration tasks consume no resource and do not
exclude other tasks. Cumulative constraints are checked at all task start events;
nonnegative demands make that sufficient without an arbitrary horizon.
Circuit and automaton witnesses are locally existentially quantified, so placing
these constructors inside negation preserves their meaning. Witness names avoid
all names occurring in the input. Expansion has explicit size limits.
The direct `regular` path compiles each input expression once. Shared constant
arrays hold transition columns; a bounded local entry index at each position
selects its source state, symbol and destination. State labels need not be
contiguous, and multiple transitions for one state and symbol remain legal.
This avoids repeating a nested data lookup for every possible transition.
The optional explicit-JSON expansion path retains its original expansion and
size limits. Both paths represent the same relation; the compact encoding does
not guarantee that a solver can decide a large projected-equivalence query.
Both full-model and direct-expression expansion enforce the same 100,000-node
JSON ceiling. `among` and `global_cardinality` estimate cross-product growth
before building repeated comparison trees, so oversized value/item combinations
are refused before their full AST allocation. The preflight includes the exact
Int guard nodes used by the finite-cardinality constructors.

The CP API has independent finite tests for circuit negation, nondeterministic
regular automata, scheduling including zero duration, lexicographic order,
negative tables, aggregate values, source preservation and variable capture.
These tests establish the exercised constructor behavior; they do not prove that
a natural-language provider selects the intended model.

`somtparser.hir_canonical.canonicalize_hir(model)` provides an optional,
separately audited syntax normalization. It returns a new model and a change
ledger: explicit `Int` decimal strings become exact JSON integers; recognized
aggregate and quantifier spellings receive the canonical constructor tag.
In provider expression slots, exact JSON integers and Booleans also become
explicit `Int` and `Bool` literal nodes. These sorts remain distinct: a bare
integer does not become a Boolean condition. Float values, ambiguous bare
strings and missing operands are not inferred. Structural numbers (bounds,
shapes, tuple projection indices and CP transition tables), explicit typed
literal payloads, source spans and opaque data retain their original roles.
Every scalar conversion has a JSON-pointer ledger entry. This provider syntax
extension does not relax the typed `HirBuilder` API, and saved candidates are
never normalized again when loaded.
Within a CP vector descriptor `{array, length, prefix}`, exact JSON integers
in `prefix` become `Int` literal nodes with individual ledger entries. Symbolic
indices keep their scope; Boolean, floating-point and string prefix values are
not interpreted as integer indices. The array shape and vector length remain
unchanged.
Real strings, source spans and unresolved interpretations are untouched. It
does not infer missing domains or repair malformed JSON. Selection must use the
normalized candidate's new digest, and experiments must retain the raw response
and report normalization separately from the original strict-schema result.

For larger HIR models, the separately versioned
`somtparser.deepseek_reasoning.DeepSeekReasoningProvider` supports the documented
DeepSeek thinking mode with high effort and a bounded 32,768-token default.
Wrap it in `CpProvider` to supply an additional CP catalog; the standard HIR
pipeline also accepts these constructors directly. This provider omits temperature
because thinking mode ignores that parameter. It saves final candidate content
and usage metadata, never reasoning text or authorization headers. Its higher
inference budget and revised typed examples form a different experiment from
the frozen 8,192-token non-thinking baseline. No accuracy improvement is implied
without measuring the full cohort.
