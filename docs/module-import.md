# Importing query-free libraries and open models

`import_module` returns a typed source artifact. It does not return a
`Translation`, expose `solve`, choose a verification property, or provide
implementations for external predicates. `translate` retains its existing
closed-query contract.

```python
import somtparser as sp

library = sp.import_module("system.moxi")
assert library.ok, library.diagnostics
print(library.systems)
initial_relation = library.relation_smt2(0, "init")

model = sp.import_module("external.fzn")
assert model.ok, model.diagnostics
print(model.unresolved)
partial_constraints = model.known_constraints_smt2()
```

The C++ entry point is `SOMTParser::Lang::importModule`, declared in
`include/somtparser/translation/module.h`. Register the languages before calling it,
as for other C++ frontend APIs. Failed imports return diagnostics and no module.
Python returns `ModuleImport`; dictionaries and lists are value snapshots.
Mutating a snapshot cannot erase a dependency from the imported artifact.

| Frontend | Imported content | Boundary |
|---|---|---|
| AIGER | Input/state variables, reset and next-state relations, constraints, output and bad-property expressions | Existing parser limitations, including unsupported justice/fairness, remain explicit |
| MoXI | Every system definition, typed current/next variables, separately retained init/trans/invariant relations, flattened subsystems | Query-free libraries only; a source with `check-system` must use `translate` |
| FlatZinc | Known declarations, domains, constraints and objective; ordered external calls with typed arguments and complete annotations | External signatures currently support Bool/Int/Real scalars and `[int]` arrays; no callback is executed or assumed |

MoXI definitions are retained in source order, including repeated names.
`relation_smt2` selects a **definition index**, not a name: two definitions of
`Delay` must remain distinguishable. A subsystem refers to the definition
visible at its defining command, matching the independently inspected
`moxi-mc-flow` reference. A later redefinition does not change an earlier
instance. Each subsystem instance receives fresh local state variables.
Every definition is checked, including unused definitions. A malformed library
is not classified merely as missing a query.

The three MoXI relations are not conjoined into a verification task. The
`relation_smt2(index, relation)` method creates an explicit **relation inspection**
script for `init`, `trans`, or `invariant`. Satisfiability of that script says
nothing about reachability or safety. AIGER imports likewise do not invent a
bad property for `empty.aag`.

For FlatZinc, overload selection checks arity, scalar/array shape, element sort,
and parameter/decision-variable status. Empty arrays retain their declared
element sort during matching. Specificity is a partial order; two
incomparable overloads are rejected. `_reif` and `_imp` external calls retain
their full source predicate names and final Boolean arguments. Known constraints
remain in the artifact alongside the unresolved calls. Filename punctuation
inside annotation strings is preserved, including `%` and `;`.

`known_constraints_smt2()` deliberately labels its output as partial and omits
`check-sat`. Satisfying its known part is insufficient to solve the source model.
The required callback filenames are dependency data, not permission to execute
them. An actual implementation or a formal relation is still needed before
these models can become closed queries.

Validation includes independent Z3 equivalence checks for the original MoXI
library relations, circuit reset/transition checks, source-domain checks for
the original FlatZinc blackboxes, and tests that preserve dependency calls and
reject malformed signatures. See `test/python/test_module_import.py` and
`scripts/audit-moxi-libraries.py`.

## Complete SMT module export

```python
module = sp.import_module("external.fzn")
assert module.ok, module.diagnostics
smt = module.to_smt2()
```

```python
with open("system.smt2", "w", encoding="utf-8", newline="") as output:
    result = sp.translate("system.moxi", module=True,
                        report="interface.json", output=output)
assert result.exit_code == 0, result.diagnostics

result = sp.translate("external.fzn", module=True)
assert result.exit_code == 0, result.diagnostics
smt = result.smt2
```

C++ callers use `Lang::exportModule(*imported.module)`. `ModuleExport` contains
`ok()`, `smt2`, `interface_json`, and diagnostics. Failed export returns no SMT
artifact. The CLI accepts `--from`, stdin and frontend `--opt` reader choices in
module mode. Query-specific `--profile` and `--dialect` are rejected. Unknown or
inapplicable module reader options fail instead of being ignored.

MoXI additionally accepts the explicit datatype dialect described in
[the frontend documentation](languages/moxi.md):

```python
module = sp.import_module("library.moxi",
    options={"flat_datatype_constructors": "true"})
```

The C++ `importModule` overload takes `ParseOptions` as its third argument.
Applied normalizations appear in the exported interface's optional
`source_rewrites` array: rule, original declaration (comments blanked), normalized
declaration, file and line. Default imports and standard spellings retain their
existing interface and SMT bytes. This records a selected source dialect; it
does not certify the nonstandard input as valid under the strict grammar.

The export contains no `check-sat` or `exit`. Each transition definition gets
separate `define-fun` exports for `init`, `trans`, `invariant`, and each AIGER
output/bad expression. All current/next state variables are explicit parameters,
in interface order; rigid declarations remain shared. Repeated source system
names remain distinct by definition index. Helpers already expanded by the
frontend remain inlined in the exported relations: this is a semantic module
representation, not a source-format round trip.

Every unresolved FlatZinc relation becomes a typed uninterpreted predicate,
and **every call is asserted**, alongside the known domains, constraints and
objective. The import identity includes the predicate name, selected signature
(including `par`/`var`), and complete annotation spelling. Thus different callback
annotations do not accidentally share an interpretation. Repeated imports with
the same identity share one SMT declaration. The consumer supplies the intended
interpretations when linking the module; the exporter neither loads a callback
nor chooses an interpretation for it.

FlatZinc arrays are encoded as finite algebraic lists, separately for each
element sort. The empty constructor and ordered `cons` chain distinguish empty
arrays, lengths, and element order without arbitrary values outside the array.
Array length is a value property, so calls of different lengths still share the
same predicate signature. The interface records the list constructors for
consumers that supply a relation implementation.

The first SMT comment is `; SOMT module interface <JSON>`. The same JSON is
available in the C++ result or CLI `--report`. It records source system names,
exported relation symbols, ordered parameter names/sorts/roles/state copies,
external symbols and typed signatures, call locations, callback annotations,
array encodings and objective count. JSON escapes line breaks and control
characters, so annotation contents cannot inject SMT commands. Export names are
fresh against source declarations.

`relation_smt2` and `known_constraints_smt2` remain inspection helpers.
`to_smt2` is the complete module export and includes external calls that the
latter helper intentionally excludes. `scripts/audit-module-exports.py` checks
the frozen 15 sources through both CLI and Python, independently parses every
artifact with Z3 and cvc5, and counts actual external call assertions. The
`--export` option of `scripts/audit-moxi-libraries.py` compares the exported
functions against the upstream MoXI parser's relations.

### Interpretation contract

For an open model, let `K` be its known constraints and let `P_j(a_j)` be its
ordered external calls under the recorded import identities. The exported
formula is `K ∧ P_1(E(a_1)) ∧ ... ∧ P_n(E(a_n))`, with the existing objective
unchanged. `E` is identity on scalars and the empty/cons encoding on arrays.
For each fixed interpretation of the imports, interpreting the exported
predicates through `E` gives the same feasible assignments and objective values.
The list encoding is injective: equal encodings require the same length and
pairwise equal elements. This contract concerns linking a supplied relation;
it makes no correctness claim about an absent external implementation.

For a transition library, each exported function is the corresponding source
relation over the listed current/next parameters and shared rigid environment.
Definitions are individually callable and none is asserted by exporting the
library. A consumer chooses the initial-state, transition, invariant, output or
bad-property combination appropriate to its verification task. The independent
33-relation experiment checks this relation-level claim for the original MoXI
libraries; it does not establish a universal proof for every frontend construct.
