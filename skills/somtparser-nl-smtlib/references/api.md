# API and artifact contracts

The bridge uses the installed `somtparser`. `catalog` records live signatures,
schema, module hashes and solver version; it does not prove universal theory
coverage. Query it on the same execution host used for validation.

| Operation | Real API | Meaning and result |
|---|---|---|
| Obtain request | `propose_nl(source, provider=capture, language="smtlib2", context=...)` | Capture exact source, hash, current schema, context and instructions at the provider boundary, without a network call |
| Construct | `propose_nl(source, provider=lambda request: model, language="smtlib2", context=...)` | `Candidate.valid`, `digest`, `diagnostics`, `diagnostic_details` |
| Bounded repair | `propose_nl_with_repair(..., provider=..., max_attempts=N, language="smtlib2", context=...)` | `ProposalTrace.attempts`; stops at first construction-valid candidate, not a semantically verified candidate |
| Load snapshot | `Candidate.from_json(text)` | Complete saved candidate |
| Export | `compile_candidate(candidate, accept_digest=candidate.digest)` | `ok`, `diagnostics`, `report()`, `to_smt2()` |
| Load target | Z3 `Optimize.from_string(script)` | All emitted assertions and objectives |
| Solve target | Z3 `Optimize.check()` | Candidate SAT/UNSAT/unknown, model and normalized objective data |

Current formal response fields (the live schema remains authoritative):

| Field | Meaning |
|---|---|
| `schema` | `somt-nl-formal-v1` |
| `language` | `smtlib2` |
| `program` | Complete SMT-LIB text |
| `decision` | `satisfiability` or `optimization` |
| `assumptions` | List of explicitly adopted conventions, not invented facts |
| `unresolved` | Remaining competing interpretations; empty when none |
| `links` | Nonempty list of `{"span":[start,end],"fragment":"exact SMT substring"}` |

Do not return `context`: the caller attaches its string-to-string map. The
`required_outputs` argument is currently HIR-only; the direct route follows
observable conventions in context without pretending it has that API contract.

Bridge operations:

- `catalog [--out file]`: live public API and schema; no LLM call.
- `request source [--context file] [--out file]`: provider-visible request.
- `link source program --quote text --fragment text [--occurrence N]`:
  exact Unicode span; repeated quotations require explicit zero-based occurrence.
- `validate source model --out new-directory [--context file]`:
  `candidate.json` and `validation.json`. Duplicate keys and NaN/Infinity are
  errors. Existing output directories are not overwritten.
- `compile candidate --digest hash --out new-directory`: `report.json` and,
  only on success, `model.smt2`.
- `check script --out new-directory [--solve] [--timeout-seconds N]
  [--memory-mib N]`: subprocess with `check.json` and worker log. Default
  wall-time 30 seconds and address-space budget 2048 MiB, both configurable.

No bridge command accepts credentials or contacts model services. The calling
agent supplies model JSON. `smt_bridge.py` retains the direct-candidate debugging
interface; `ir2smt.py` is the three-route production entrypoint. Its HIR request
includes the real `hir_api()` constructor catalog. See [routes.md](routes.md).
The check/solve command is developer-side only, not a production translation step.

For agent use, `ir2smt.get_request(source, context, route)` captures the contract;
`capability_index(route, request)` lists available groups without their bodies.
`materialize_capabilities(route, ids, request)` returns a hashed packet whose
`request` contains the selected schema/API view and document texts. Only `core`
is implicit. The source/context are preserved; the complete native schema stays
available to the compiler. See [progressive protocol](progressive-protocol.md).

`ir2smt.render` also accepts exact source anchors in supported span fields:
`{"quote":"an exact source phrase","occurrence":0}`. It resolves these to
numeric spans before native compilation and records the resolution ledger.
Absent or repeated quotes without an occurrence fail explicitly. This extension
belongs to the three-route wrapper; raw native APIs still use numeric spans.
