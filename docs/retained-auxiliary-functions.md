# Retaining large generated function definitions

A parameterized HIR function uses `define-fun-rec` when its estimated transitive
inline expansion reaches 512 operations. This includes source-visible functions
and chains of small helpers. The estimate follows dependency order, counts
distinct body nodes, and treats already retained callees as single calls. Small
expansions and nullary definitions retain ordinary `define-fun`. The existing
cycle check proves that these retained bodies are acyclic. This threshold chooses
an output representation; it does not reject or approximate a model. Each
selection is recorded as `retained-acyclic-definition` in the translation report.

The SMT-LIB2.6 standard, Section4.2.3, gives function-definition commands their
universal defining equations. For an acyclic body, both forms determine the same
unique total function, including free global dependencies. Fresh parameter
renaming and dependency order are preserved. No source constraint, objective or
body equation is removed, and no recursive source program is introduced.
[SMT-LIB2.6 reference](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf).

This representation allows Z3 to retain function applications during parsing
instead of expanding ordinary macros at every call. It may change later solver
performance, and does not guarantee a definitive solver answer. The output
consumer must support standard `define-fun-rec`. The ordinary and retained
printers both use scope-safe let sharing where applicable.
[Z3 recursive-function design](https://github.com/Z3Prover/z3/blob/master/doc/design_recfuns.md).

Qualification results belong in the evidence capsule; saved-target diagnostics
alone are not conversion coverage or semantic-equivalence benchmark results.

When parsing independent generated scripts with Z3's Python API, use a fresh
`z3.Context()` per script and construct that script's solver and expressions
in the same context. Recursive-function definitions belong to the Z3 context,
so different solver objects sharing its default context do not isolate them.
The official worker already uses a new process for each independent target.
