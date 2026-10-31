# Exact function definitions in HIR candidates

HIR function entries remain uninterpreted declarations when they contain only
`name`, `arguments`, and `result`. An exact definition adds `binders`, `body`,
and `span` together:

```json
{
  "name": "twice",
  "arguments": ["Int"],
  "result": "Int",
  "binders": [{"name": "n", "sort": "Int"}],
  "body": {"op": "add", "args": [{"var": "n"}, {"var": "n"}]},
  "span": [0, 16]
}
```

Here the candidate source is `twice(n) = n + n` (16 code points).

The span is a nonempty half-open range of Unicode code points in the exact
source string, using the same bounds checks as constraint spans. Each binder's
sort must be the corresponding argument sort, and the body must have the
result sort. Binder names are lexical: they may shadow model declarations,
and nested quantifiers may shadow and restore them. All signatures are declared
before bodies are checked, so a body can reference a later definition. Cycles
are rejected by native HIR validation. A body is an exact term definition; it
does not add an independent constraint or assert that the source text entails
that interpretation. Candidate JSON remains caller-owned and compilation uses
the selected immutable snapshot.

Bodies use the existing acyclic HIR term-definition contract. Native `GLOBAL`
constraints inside a definition remain unsupported because their rewrites may
introduce witnesses requiring a separate local scope; see
[the native definition boundary](hir-defined-functions.md). Definitions do not
turn source-location checks into proof of natural-language correctness.
