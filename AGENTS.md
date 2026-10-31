# Repository guidance

## Project and layout

SOMTParser is a solver-independent C++17 SMT-LIB/OMT frontend with Python
bindings. Read `README.md` and `docs/source-layout.md` for the current design.

- `include/somtparser/` and `src/`: public headers and C++ implementations.
- `core/`, `ir/`, `context/`, `passes/`, `frontend/`, `model/`: the SMT parser,
  typed DAG, transformations and model evaluation.
- `hir/`: shared typed constraint representation and construction APIs.
- `translation/`: language registry, profiles, diagnostics and pass pipeline.
- `lowering/`: HIR encoding into the SMT DAG and target dialects.
- `languages/`: optional language frontends and their input fixtures.
- `python/`: pybind11 bindings, Python package and public `.pyi` stubs.
- `tools/`: optional PDDL and semantic validation helpers.
- `test/`: C++ tests, Python tests and semantic checks.

The translation path is language frontend -> HIR -> shared encoding -> SMT DAG
-> SMT-LIB/OMT. Some compact paths stream output; native SMT-LIB parsing can
construct the SMT DAG directly. Use `hir/` and `translation/` header paths;
historical C++ namespace names containing `Uir` remain public API.

File conversion is the public `translate` API in `translation/translate.h`, linked
with `SOMTParser::languages`, and `somtparser.translate` in Python. There is no
standalone converter executable or console script. Keep conversion/report
policy in that library implementation and Python bindings limited to adapters.

## Build and validation

Once a change is ready and necessary checks give reasonable confidence,
commit and push it without waiting for a full local build or remote CI.
Choose checks appropriate to the change; a full C++ suite is not a mandatory
pre-commit gate. Do not additionally build/install Python packages, run
Python-version matrices, or dispatch/wait for wheel builds unless the user
explicitly requests them for the current task. When full C++ validation is
needed, use the `CI Tests` configuration in `.github/workflows/ci.yml`:
Debug, all C++ tests and tools enabled, warnings as errors, two workers.
This checkout uses `develop` on `origin`; do not force-push over unrelated
remote changes. Report checks actually run and distinguish focused checks
from full CI validation. Fix known failures before considering work complete.

Dependencies: C++17 compiler, CMake 3.16+, GMP and MPFR. Python bindings also
require Python 3.9+ and pybind11; packaging uses scikit-build-core.

Reuse one persistent incremental build directory per project. Prefer the
existing configured directory, honoring `SOMTPARSER_BUILD_DIR`; otherwise the
test script defaults to `build/`. Do not create separate build trees per
experiment, feature, date, retry or Python build. Serialize writers sharing a
build directory and preserve its generator and relevant configuration.

```bash
# Full CI-equivalent C++ validation when needed.
CMAKE_BUILD_TYPE=Debug SOMTPARSER_WARNINGS_AS_ERRORS=ON SOMTPARSER_BUILD_JOBS=2 ./test/run_all_tests.sh

# Focused C++ check; substitute the existing directory and test name.
ctest --test-dir "${SOMTPARSER_BUILD_DIR:-build}" -R 'SOMTParser.test_name$' --output-on-failure

```

`run_all_tests.sh` enables tests, tools and warnings as errors; its build type
defaults to Debug and can be overridden with `CMAKE_BUILD_TYPE`. Python builds
need `BUILD_PYTHON=ON` and `SOMTPARSER_BUILD_LANGUAGES=ON`. Ensure imports resolve
to an extension built from the current source before trusting Python results.

C++ tests are discovered from `test/**/*.cpp` and registered as
`SOMTParser.<file_basename>`. Run standalone test binaries from the repository
root because fixtures use relative paths. Focused checks are useful during
development and may be sufficient for a scoped change. Language documentation
citations can be checked with `python scripts/check-doc-citations.py`.

## Implementation invariants

- Nodes are hash-consed. Rebuild through `NodeManager` rather than mutating a
  shared `DAGNode`.
- Builders simplify and canonicalize expressions, including commutative child
  order. Tests should account for simplification and check semantics.
- `NODE_KIND` ordering and `NUM_KINDS` drive dispatch tables. Respect the
  marked contiguous operator section when adding kinds.
- Use `condAssert` for library checks that must survive Release builds, and
  `VERIFY` from `test/test_helpers.h` for test expectations with side effects.
- `Parser::assert()` conflicts with the C assertion macro; account for header
  ordering when using `<cassert>`.
- Parsing failures use `ParseErrorException` internally; public `parse()` and
  `parseStr()` return `false` on caught parse errors.
- Preserve symbol-resolution order and deterministic declaration output.
- When changing public APIs, update the appropriate public headers, bindings,
  `.pyi` stubs and documentation together. Core APIs use the umbrella header
  `include/somtparser/parser.h`; HIR/translation also have dedicated headers.
- `test/instances/error_*.smt2` are historical regression fixtures expected to
  parse successfully, despite their filenames.

## Workspace and storage preferences

- Preserve user changes and historical provenance. Use the current requested
  branch. The user has authorized committing and pushing changes once ready
  after necessary checks, without waiting for full builds or remote CI.
- Before large operations, check actual Windows C: free space as well as Linux
  free space. WSL virtual disk size is not physical free capacity. Do not impose
  arbitrary cache quotas, move Ubuntu or stop WSL for cleanup.
- Never delete unique sources, research evidence, chat history or personal
  documents. Remove only verified obsolete/reproducible build data, with a
  verified archive when needed. Preserve revisions/hashes, validation logs and
  explicitly needed frozen binaries rather than whole build trees; prefer D:
  for large archives.
- Reuse immutable SMT-LIB 2025 archives at
  `/mnt/d/D_Work/ISCAS/datasets/smtlib-2025` (Windows
  `D:\D_Work\ISCAS\datasets\smtlib-2025`). Read their README/manifest for
  provenance. The stored non-incremental QF_BV, QF_LIA, QF_LRA, QF_NIA and QF_NRA
  archives are a subset of the release; do not make per-project copies.
- For related FOSO native Z3 work, use
  `/home/fuqi/.cache/foso/native-builds/current` and
  `python -m experiments.z3_native_fol.build` without per-experiment `--output`
  or `--reuse-build`. Current tests use `current/build/z3_fol`; retain explicit
  frozen-binary environment overrides and original archive provenance.
