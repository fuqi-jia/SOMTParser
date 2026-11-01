# Native SMT source layout

`main` provides the C++17 SMT-LIB/OMT frontend and its Python bindings.

| Directory under `include/somtparser/` and `src/` | Responsibility |
| --- | --- |
| `core/` | Kinds, utilities, assertions and timing |
| `ir/` | SMT expression DAG, sorts, values and exact numbers |
| `context/` | Hash-consed node construction and expression managers |
| `frontend/` | SMT-LIB/OMT parsing, symbols, commands, objectives and streaming output |
| `passes/` | Traversal, rewriting and formula transformations |
| `model/` | Solver model parsing and evaluation |

The native path is SMT-LIB/OMT input -> typed SMT DAG -> analysis,
transformation or SMT-LIB/OMT output. Include `somtparser/parser.h` for the
public parser API. Link `SOMTParser::somtparser` for the frontend or
`SOMTParser::somtparser_ir` for the independently usable IR/numeric library.

`python/bindings.cpp` exposes the native API. The package initializer and
public type stubs live in `python/somtparser/`. Native C++ tests are in
`test/`, with Python binding tests under `test/python/`.

Future language frontends, HIR, translation, lowering and natural-language
modeling are maintained on [develop](https://github.com/fuqi-jia/SOMTParser/tree/develop).
They are excluded from main's source, build and Python API.
