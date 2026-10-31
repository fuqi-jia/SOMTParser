# Core API migration notes

These notes cover changes from public SOMTParser main `f730eaac` (2026-09-16).
Rebuild and relink C++ applications and Python extensions when updating: the
parser and DAG classes do not provide a stable binary ABI.

## Unified translation result

The `somt-convert` executable has been removed. Python callers use
`somtparser.translate(path, language=..., dialect=..., options=...)`; C++ callers
include `somtparser/translation/translate.h` and link `SOMTParser::languages`.
Conversion output, formatted diagnostics and status are returned together;
large outputs can stream to caller-owned sinks. `Translation.diagnostics` is
formatted text; structured diagnostic objects are available as
`diagnostic_items`. `details=False` disables optional inspection data while
retaining the same result type and completed output. See [the translation API and
experiment migration table](translate.md) for all settings and status codes.

## HIR and translation header paths

The former `uir/` implementation is organized into `hir/` (the constraint
representation and construction APIs) and `translation/` (the translation
pipeline). For example, replace `somtparser/uir/hir.h` with
`somtparser/hir/hir.h`, and `somtparser/uir/translate.h` with
`somtparser/translation/translate.h`. The old header paths have been removed;
callers must use the new paths. C++ namespaces, signatures and Python APIs
are unchanged. See [the module layout](source-layout.md) for the complete
division of responsibilities.

## Floating-point values to bit vectors

The legacy `FloatingPointUtils::fpToUbv(string, Integer)` and
`FloatingPointUtils::fpToSbv(string, Integer)` functions are removed. They sliced
characters from a hexadecimal string rather than performing a numeric
floating-point conversion. Their arguments supplied neither the source FP
format nor a rounding mode, so preserving their signatures cannot preserve a
well-defined SMT-LIB numeric conversion.

Construct a typed floating-point term and pass an explicit rounding-mode node:

```cpp
// rm: a rounding-mode node; fp: a floating-point node; width: an integer node.
auto unsignedResult = parser.mkFpToUbv(rm, fp, width);
auto signedResult = parser.mkFpToSbv(rm, fp, width);
```

The corresponding Python operations are `parser.fp_to_ubv(rm, fp, width)` and
`parser.fp_to_sbv(rm, fp, width)`. The FP node carries its exponent and
significand widths. Specify the intended format and rounding policy in the
calling application; do not infer them from the number of hexadecimal digits.

For direct constant evaluation, `FloatingPointUtils::fpValueToUbv` and
`fpValueToSbv` accept an `FPValue`, a target bit width, and an MPFR rounding mode.
They return an optional decimal bit-vector value. An empty optional means that
the helper did not produce a valid constant; retain the symbolic conversion
rather than substituting zero. A negative signed result is represented in
unsigned two's-complement form at the target width.

## Quantifier builders and serialization

C++ vector-based `mkForall` and `mkExists` keep the existing body-first contract:
`{body, variable1, variable2, ...}`. Python convenience methods take variables
and then the body. This is not an API reorder.

`DAGNode::toString()` returns the node's raw name. Use `Parser::toString(node)`
or `dumpSMTLIB2(node)` for SMT-LIB serialization, including symbol quoting.

The integrated language frontend adds dialect-aware whole-problem output.
Its `dumpSMT2()`/`dump_smt2()` snapshots include live objectives and soft
constraints. A snapshot is not a replay of the complete incremental command
history. Code that needs command ordering should use the ordered command API.
