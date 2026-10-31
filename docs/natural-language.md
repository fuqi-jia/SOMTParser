# Natural-language modeling (core input path)

The language-configuration route and dataset contracts are documented in
[nl-datasets-and-model.md](nl-datasets-and-model.md). It supports explicit
MiniZinc, LP, XCSP3 and SMT-LIB proposals in addition to the typed grammar below.
Natural-language formalization is part of the core architecture.

## Direct SMT-LIB and optional HIR proposals

An agent can generate SMT-LIB directly with
`propose_nl_with_repair(..., language="smtlib2", max_attempts=N)` and export the
selected candidate with `compile_candidate`. This route checks the complete
program through the native frontend and checks the decision against its actual
objectives before repair stops. Syntax, type, and decision errors enter the
same immutable-candidate feedback loop. No solver is called by validation.
The compiler still uses its shared internal representation; the agent does
not have to generate HIR JSON first.

The skill recommends direct SMT-LIB for ordinary logical and arithmetic models.
HIR remains useful when its CP globals, finite folds, shaped arrays, and output
contracts make a model easier to construct. Neither representation guarantees
better natural-language accuracy; schema or compiler acceptance cannot establish
that all source requirements were modeled correctly.

## Agent workflow through native HIR

For unrestricted text, the native HIR route is `source → provider HIR JSON →
HIR construction/type checking → shared lowering → SMT`. The provider receives
the current schema and constructor guidance; `hir_api()` exposes the complete
machine-readable catalog. `propose_nl_with_repair(..., language="hir")` can
return located construction feedback to the provider. Its repair loop does not
consult reference answers or solver verdicts.

The repository includes the [somtparser-nl-hir skill](../skills/somtparser-nl-hir/SKILL.md).
Its executable bridge provides `request`, `validate`, and `compile` commands
using the public Python API. `request` and `validate` accept `--language smtlib2`
or `--language hir`; the omitted-option default remains HIR for compatibility.
The calling agent generates the selected format's JSON envelope, so
the skill does not require an additional model service or MCP server. A selected
candidate digest binds export to the exact validated snapshot. Construction
success, complete target loading, and source/target semantic validation remain
separate results; skill packaging itself supplies no accuracy guarantee.

The controlled typed grammar described below is a separate input configuration
and retains its SMT-LIB adapter path.

## Typed configuration and interpretation boundaries

The typed configuration implements `text → typed candidate → selected
interpretation → SMT-LIB parser → HIR → configured lowering → SMT/OMT`.
It reuses the existing `smtlib2` language adapter. It is not a new C++ registry
language, nor an unrestricted natural-language understanding model. Its built-in
provider is a deterministic English/Chinese controlled grammar. A callback can
supply candidates from an external language model; no network service or model
weights are bundled, and no external model is called by default.

## Run a translation

Install the Python package with `python -m pip install .` (or `-e .` for development).
Use one statement per line; terminal `.` and `。` are optional.

```text
设x为整数，范围为0到10。
x至少3。
最小化x。
```

```sh
somt-nl translate examples/natural_language/ok/optimization.zh.txt --report report.json > model.smt2
z3 model.smt2
```

The output includes `(minimize nl_s0)` and constraints `0 ≤ nl_s0 ≤ 10`,
`nl_s0 ≥ 3`. Z3's optimum is 3. Translation emits a solver script; it does not
run a solver. Z3 is the default OMT dialect. SMT-only output can use `--dialect
none`, which rejects objectives instead of silently removing them.

```python
import somtparser as sp
result = sp.translate_nl("Let x be an integer between 0 and 10.\n"
                         "x is at least 3.\nMinimize x.\n")
if not result.ok:
    raise ValueError(result.diagnostics)
print(result.to_smt2())
print(result.report())
print(result.project_assignment({"nl_s0": 3}))  # {"x": 3}
```

## Controlled grammar v1

Every nonempty line must be recognized. Unknown text, undeclared symbols,
incompatible types, unresolved candidate alternatives and conflicting decision
requests prevent emission. The grammar is a restricted language with fixed
meaning, not a guess about unrestricted prose. Keywords in English are
case-insensitive; identifiers are case-sensitive. Use simple identifiers that
do not contain keywords. `true`, `false`, `and`, `or`, `not`, `ite`, and `tdiv`
are reserved. Declarations are collected before expressions are type-checked.
Identifiers containing Chinese operator or control phrases are rejected, so
rewriting an operator cannot silently change part of a declared variable name.

| Construct | English | Chinese |
|---|---|---|
| Integer | `Let x be an integer between 0 and 10.` | `设x为整数，范围为0到10。` |
| Real | `Let y be a real between 0.0 and 1.0.` | `设y为实数，范围为0.0到1.0。` |
| Boolean | `Let b be a boolean.` | `设b为布尔变量。` |
| Finite domain | `Domain Person consists of Alice, Bob.` | `域Person包含Alice、Bob。` |
| Empty domain | `Domain Empty is empty.` | `域Empty为空。` |
| Domain variable | `Let p be a Person.` | `设p为Person类型变量。` |
| Predicate | `Predicate likes has arguments Person, Person.` | `谓词likes的参数类型为Person、Person。` |
| Universal | `For every x in Person, likes(x,Alice).` | `对于每个x属于Person，likes(x,Alice)。` |
| Existential | `There exists x in Person such that likes(x,Alice).` | `存在x属于Person使得likes(x,Alice)。` |
| Implication | `If b, then x >= 1.` | `如果b，那么x至少1。` |
| Feasibility | `Find a solution.` | `求一个解。` |
| Validity | `Prove that x >= 0.` | `证明x至少0。` |
| Objective | `Minimize x.` / `Maximize x.` | `最小化x。` / `最大化x。` |
| Objective order | `Optimize lexicographically.` | `按字典序优化。` |

Numeric bounds are optional. Expressions support `+ - * /`, comparisons
`= == != < <= > >=`, `and or not`, exact decimal literals, parentheses,
`ite(condition,then,else)` and `tdiv(a,b)` (integer division toward zero).
Predicate application uses `likes(x,Alice)`. Some verbal operators are accepted,
including `is at least`, `is at most`, `is equal to`, `plus`, `minus`, `times`,
`divided by`, `至少`, `至多`, `等于`, `并且`, `或者`, `并非`.
Expressions follow ordinary Python arithmetic/comparison/Boolean precedence;
parentheses make grouping explicit. The parser only inspects an allowlisted AST:
it never evaluates Python code. Quantifiers nest explicitly in their body.
Several objectives require an explicit lexicographic order, with priorities
following their source order. Pareto/box, soft constraints, pronoun resolution,
implicit units, probabilistic statements and unrestricted quantification are
outside this extension's current fragment.

## A typed language configuration

`candidate_schema()` exposes `nl_model.schema.json` to providers. A model carries
`schema=somt-nl-model-v1`, `semantics=relational-v1`, an explicit `decision`,
domains, typed symbols, constraints, objectives/order, an optional validity goal,
assumptions and unresolved interpretations. Every declaration, constraint,
objective and goal has a half-open `[start,end]` Unicode code-point span into the
exact input text. Span validation establishes location validity, not semantic
entailment by that text. Reports preserve these links and source/digest hashes.
The compiler checks types and semantic restrictions in addition to JSON shape.

`Int` means unbounded mathematical integers and `Real` exact mathematical reals.
Real literals in provider JSON must be decimal or rational strings, not binary
floats. Finite domains use explicit named members, encoded as disjoint *typed*
integer ranges: the candidate checker prevents equality/application across
unrelated domains. Quantifiers are guarded by their domain range. Universal
quantification over an empty range is true and existential quantification is
false; a scalar variable of an empty domain makes the model infeasible.
There is no implicit nonemptiness, machine-width bound, distinctness axiom for
unrelated objects, or quantifier reordering.

Partial arithmetic uses a definedness/value pair. Relations incorporate operand
definedness; logical operators combine those resulting Boolean values. Thus
`tdiv(7,0) = 0` and `tdiv(7,0) != 0` are false, while `not (tdiv(7,0) = 0)` is true.
An `ite` requires only its selected numeric branch to be defined. Objectives
require defined values. These are explicit `relational-v1` conventions, not
claims about the unique meaning of informal arithmetic.

The adapter now carries plain numeric minimize/maximize objectives into HIR.
Multiple SMT-LIB objectives require `:opt.priority lex`. The SMT reader also
preserves a single `assert-soft` cost group with exact positive integer weights.
Mixed soft/explicit objectives, multiple soft groups, unsupported priorities,
and custom comparison/epsilon/M remain refused; the lower-level parser retains
its broader OMT syntax support. This reader improvement does not add a new
natural-language interpretation rule. See [the SMT reader contract](languages/smtlib2.md).

## Plug in a free-text proposal provider

```python
from somtparser.natural_language import propose_nl, compile_candidate, Candidate

# Your service adapter accepts source/schema/instruction and returns a model dict.
# provider(request) must return typed AST data, not code or an SMT script.
candidate = propose_nl(user_text, provider=my_service_adapter)
print(candidate.to_json())   # inspect model, assumptions and unresolved choices
# Select the exact reviewed snapshot. Do not regenerate it after review.
result = compile_candidate(candidate, accept_digest=selected_digest)
```

The request contains `source`, `source_sha256`, `schema`, and `instruction`.
A provider is responsible for credentials, API calls, timeouts and its own model
metadata. The provider's callable name is recorded; service model/version,
prompt revision and decoding settings should be recorded by the adapter in
candidate assumptions or a separate experiment record. This extension does not
pretend to capture those details automatically. A missing or mismatched digest
returns a pending interpretation and produces no SMT. Even a schema-valid
external candidate is not automatically accepted. Unresolved choices must be
resolved in the model, generating a new digest, before compilation.

### Caller-owned HIR output contracts

When an application already knows the required observable names and shapes,
pass that contract explicitly for HIR proposals. Each entry has exactly a name,
HIR sort and shape; the API checks declarations after normal HIR validation and
reports mismatches without inventing, renaming or resizing declarations.

```python
from somtparser import propose_nl, compile_candidate

outputs = [{"name": "visits", "sort": "Bool", "shape": [4, 5]}]
candidate = propose_nl(
    source_text, language="hir", context={}, provider=my_provider,
    required_outputs=outputs,
)
print(candidate.diagnostics)  # missing/duplicate/wrong-signature outputs
result = compile_candidate(candidate, accept_digest=candidate.digest)
```

The contract is caller-owned input, is sent as a top-level provider request
field, and is included in the candidate envelope and digest. Repair attempts
receive the same unchanged contract. Loading and explicitly compiling a saved
candidate rechecks it. Calls that omit `required_outputs` retain their existing
request shape and digest; the option is currently HIR-only.

For `language="hir"`, the provider schema specifies objective directions as
`minimize` and `maximize`. A newly proposed objective may also spell these as
`min` and `max`; canonicalization records each exact alias in
`candidate.normalization_ledger` before computing the candidate digest. It
preserves objective expressions, order, source spans and unresolved choices.
Other direction strings are not guessed, and absent objectives are not inferred.
Loading an existing `Candidate` never applies new normalization rules: its
archived model and digest remain unchanged.

A snapshot can be saved and selected independently of the proposing process:

```sh
somt-nl propose examples/natural_language/ok/allocation.en.txt > candidate.json
somt-nl compile candidate.json --accept-digest DIGEST_FROM_REVIEW --report report.json > model.smt2
```

Saved candidates bind source, model and provider to a digest. A digest prevents
accidental selection of a changed snapshot; it is neither authentication nor a
proof of interpretation correctness. `translate_nl` without a provider directly
uses the explicitly chosen controlled grammar. Loading a saved candidate always
requires digest selection, even if its provider field names the built-in grammar.

## Result meaning and evidence

A validity request encodes `constraints ∧ ¬goal`. Consequently UNSAT means valid
under the selected assumptions and SAT means invalid. Feasibility/optimization
SAT means feasible; SAT alone does not establish optimality. Use
`result.interpret_solver_answer("sat" | "unsat" | "unknown")`; it checks the
formal translation's soundness/completeness flags before interpreting a decisive
answer. A translation carrying bounds does not produce an unconditional verdict
through this helper; inspect the formal report's bounds instead. `unknown`
remains unknown. No solver is run by this helper.

`project_assignment` decodes exact scalar values using the generated symbol map;
finite-domain integers become source member names. It does not validate all
source constraints or decode predicate interpretations. Supply exact Python
`int`, `bool`, `Fraction` or rational strings as appropriate; no float rounding.

`replay_assignment` (since 2026-09-19) is the source-witness replay: it takes
the decoded shape `project_assignment` returns and substitutes the values into
the typed candidate's own ASTs — not the emitted SMT — under the same
relational semantics the compiler encodes, so a wrong encoding or projection
cannot validate itself. Arithmetic is rational; a constraint holds iff its
terms are defined and its value is true; `ite` counts only the taken branch's
definedness; quantifiers enumerate their explicit finite domains; truncating
division follows the encoding's sign rule. Declaration bounds and domain
membership are checked as source constraints, and an undefined objective is a
violation, not a value. The report is factual — `{holds, violations, goal,
objectives}` with per-violation kind (`bound`/`domain`/`constraint`/
`objective-definedness`) and source-span evidence; interpreting validity
polarity or optimality stays with the caller. Constraints applying a
predicate are refused by name: a predicate's witness is an interpretation the
replay does not decode, which remains future work.

Reports separate selected interpretation/provenance from the existing formal
translation report. `intent_preservation=not-proved` always: an exact formal
lowering is conditional on the selected formal model, not evidence that an LLM
understood a requirement. The translation profile still controls formal passes.

Limits bound input text (128 Ki characters), candidate JSON (1 Mi characters),
AST visits (10,000), depth (64), list entries (1,024), predicate arity (16), and
expanded expression size (1 Mi characters, with a 4 Mi-character cumulative
intermediate rendering budget). Unsupported constructs are diagnosed;
there is no fallback that omits a constraint merely to obtain SAT.

## Regression checks

```sh
python -m pytest test/python/test_natural_language.py -q
SOMTPARSER_BUILD_JOBS=4 ./test/run_all_tests.sh
python -m pytest test/python -q
```

The Python tests run Z3 and cvc5 when available. They check known mathematical
answers for exact arithmetic, relational division-by-zero, empty domains,
quantifier reversal, validity polarity and Z3 optimization; they also exercise
snapshot selection/tampering, typing and CLI failure behavior. Solver-dependent
tests skip when the corresponding executable is absent. These are small
regression cases, not a held-out evaluation of unrestricted NL accuracy.

## DeepSeek proposal provider

An optional `DeepSeekProvider` now implements the service callback. It uses the
[official Chat Completions endpoint](https://api-docs.deepseek.com/api/create-chat-completion/)
and [JSON output](https://api-docs.deepseek.com/guides/json_mode/). It sends only
the supplied source, schema, source-line offsets and formalization instructions;
it does not read repository files or send conversation history. Its API key is
an HTTP bearer credential, never part of the prompt or candidate.

Load `DEEPSEEK_API_KEY` through your secret manager or a hidden shell prompt.
For an interactive Bash shell:

```bash
read -rsp 'DeepSeek API key: ' DEEPSEEK_API_KEY
export DEEPSEEK_API_KEY
somt-nl propose request.txt --provider deepseek > candidate.json
unset DEEPSEEK_API_KEY
# Inspect the actual candidate, assumptions, unresolved choices and digest.
somt-nl compile candidate.json --accept-digest REVIEWED_DIGEST > model.smt2
```

There is deliberately no `--api-key` command-line argument or credential file.
The library also accepts an in-memory key. Do not embed credentials in scripts.

```python
from somtparser import propose_nl, compile_candidate
from somtparser.deepseek import DeepSeekProvider

provider = DeepSeekProvider()  # reads DEEPSEEK_API_KEY
candidate = propose_nl("请选一个0到10之间且不小于3的整数x，让x尽可能小。", provider=provider)
print(candidate.to_json())
print(provider.last_metadata)  # model, token counts, hashes, elapsed seconds
# Only after reviewing this snapshot:
result = compile_candidate(candidate, accept_digest=reviewed_digest)
```

The default model is `deepseek-flash`; set `DEEPSEEK_MODEL`, CLI `--model`, or
constructor `model=` explicitly to select another available compatible model.
The adapter fixes non-thinking mode, JSON output and requested temperature zero;
[DeepSeek's current thinking-mode documentation](https://api-docs.deepseek.com/guides/thinking_mode/)
explains the explicit switch. It defaults to `max_tokens=4096` and a 60-second
socket timeout, both configurable in Python. The socket timeout is not an overall
request deadline. One proposal makes exactly one API call, with no automatic
retry or solver-driven rewrite. Redirects are refused. The response-size cap is
2 MiB, with the existing stricter candidate JSON limits still enforced.

HTTP authentication/balance/rate-limit errors, transport failures, truncated
responses, empty content and malformed JSON produce sanitized `DeepSeekError`
exceptions. Error bodies and credentials are not printed. Valid JSON must still
pass SOMTParser's semantic/type/span checks. A valid candidate still requires
explicit interpretation selection; no provider result compiles automatically.

A digest-bound `Provider execution record` is appended to candidate assumptions.
It records prompt version, requested/returned model names, decoding settings,
request/content hashes and available token counts; it is provenance, not a
semantic assumption or correctness certificate. `last_metadata` additionally
contains local elapsed time and resets for every call. Model names may be service
aliases and are not immutable weight/version identifiers. Full service response
bodies and reasoning traces are not persisted by the adapter.

Offline tests in `test/python/test_deepseek_provider.py` mock the transport and
exercise success, review gating, errors, limits, provenance and credential
handling. They make no network calls. Running an actual proposal is opt-in,
billable, and submits that input text to DeepSeek.
