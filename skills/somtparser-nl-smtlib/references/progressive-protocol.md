# Progressive skill protocol

Use the same mechanism for HIR, direct SMT and hybrid. Resources include native
API fragments, semantic interpretation, CP/linear/FOL guides, macros, templates,
dialects and diagnostics. The resource directory is source-independent. Selection
uses only the exact task and fixed caller context, never reference solutions.

## Calls and retrieval

1. The caller captures the live native request, keeping the complete schema on
   disk. The first API call sees source, context, route and resource descriptions.
2. The model returns `{"action":"lookup","resources":["arithmetic","bool","domain.linear","protocol.candidates"]}`.
3. Deterministic code retrieves those IDs, derives the applicable schema/API view
   from the live contract and records hashes. It sends the original source and
   context again with that view and selected document text.
4. The model returns the complete native route candidate directly, or requests more
   resources with another lookup. Previously retrieved resources remain available;
   the full unselected catalog is never automatically appended.
5. The caller compiles the candidate. A construction error may trigger a complete
   replacement candidate, including another lookup if needed. No semantic oracle
   feedback enters this process.

`core` loads implicitly, including one small complete format example for the
selected route. The basic output contract must not depend on choosing an optional
guide; domain/API/macro details remain retrievable. The generation schema puts the native candidate first and permits lookup only
for IDs not yet loaded. Unknown IDs and repeated lookups that add no resources
produce precise diagnostics. Legacy wrapped candidates are accepted as input
for compatibility; new prompts do not require that extra envelope. Missing resources are not evidence a source feature is
unsupported. All candidate root fields remain present in the advertised schema;
only optional operator/sort branches are narrowed to what has been retrieved.
The native compiler keeps its complete support and remains authoritative.

This is a structured lookup protocol over ordinary JSON completions, not a claim
that a remote model has filesystem or native tool-call access. Agents that can
read files may instead invoke `capability_pack.py index/read` directly.

## Injected transport

```python
from progressive_provider import ProgressiveProvider

agent = ProgressiveProvider(caller_provider, result_directory, max_calls=5)
candidate = agent(native_request)
# Caller invokes ir2smt.render; construction feedback can be attached to
# native_request['repair'] before invoking this same agent again.
```

The injected provider owns the endpoint and credentials. It exposes `model`,
`last_request`, `last_response_content`, `last_metadata` and a callable accepting
a proposal. This module owns no credentials, network transport or solver. The
SOMTParser compatible provider recognizes `protocol: somt-skill-agent-v2` and
switches between selection-only and native-candidate generation instructions.
The initial phase returns a lookup; later lookups are optional. Source, context,
route and target dialect are bound throughout the session.

Five is the pilot's total model-call budget, not five retries per phase. The same
counter covers initial selection, further lookups, candidates and outer repairs.
Source, context and route cannot change during a session. Transport failures are
not replayed automatically. The caller distinguishes an unreturned API response
from a complete response with malformed syntax.

## Evidence and costs

Each `skill-rounds/NNN/` preserves the proposal, provider request, raw response,
usage and phase. Lookup rounds also preserve the retrieved packet, document/API
hashes and unchanged source/context. Candidate attempts preserve compilation and
independent evaluation separately. Credentials are never serialized.

`last_metadata.usage` sums physical calls made during the current invocation only;
`total_provider_calls` tracks the full session. Summing invocation totals therefore
does not count earlier selection twice when construction repair is attempted.
Unknown API usage stays unknown. Report total input/output tokens, number of calls,
latency, construction success and independent semantic results; shorter individual
prompts alone do not prove lower total cost.

## Current boundaries

Documents are retrieved as whole files; theory APIs and schema alternatives are
selected at constructor-group granularity. Dialect IDs currently share one
comparison document. This implementation does not yet evict previously selected
resources or create separate per-clause model calls. It narrows the available
library to a task-specific working set, then grows that set only on demand.

Pure translation never executes a solver. Full/compact one-shot prompts remain
explicit comparison treatments; do not replace frozen requests mid-experiment.
