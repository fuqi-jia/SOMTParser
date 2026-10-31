# HIR and translation modules

HIR is the shared constraint representation. `translation/` contains the
pipeline that operates on it; it is not another intermediate representation.

| Directory under `include/somtparser/` and `src/` | Responsibility |
| --- | --- |
| `hir/` | Typed expressions, declarations, constraints, objectives, feature vocabulary, type checking, compact storage and planning construction APIs |
| `translation/` | Language interface and registry, encoding profiles, pass orchestration, diagnostics, semantic contracts, reports and translation/module entry points |
| `lowering/` | Encode HIR into the existing SMT representation and emit target dialects |
| `ir/` | The original SMT expression DAG, sorts and values |

The main language translation path is:

```text
language frontend -> HIR -> shared encoding -> SMT DAG -> SMT-LIB / OMT
```

Compact clause and linear-row paths may stream output without materializing the
entire SMT DAG. The native SMT-LIB parser can construct the SMT DAG directly.
Neither path introduces a separate UIR representation.

Use the headers matching the API you need:

```cpp
#include <somtparser/hir/hir.h>
#include <somtparser/hir/typecheck.h>
#include <somtparser/translation/translate.h>
```

The C++ namespaces (`SOMTParser::Uir::Hir`, `SOMTParser::Uir`
and `SOMTParser::Lang`) and public Python APIs are unchanged. Header paths use
`hir/` and `translation/` exclusively; update existing includes to these paths.
There are no forwarding headers or implementation under `uir/`.
Module tests live in `test/hir/` and `test/translation/`; existing test executable
names are retained so CI filters and historical records still identify them.
