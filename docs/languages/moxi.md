# MoXI - hierarchical symbolic transition systems

**Audit date**: 2026-08-25
**Status**: bounded finite-query translation is implemented in `languages/moxi/`;
fairness is encoded by bounded lassos; simultaneous grouped results are refused.

Query-free libraries can additionally use [typed module import](../module-import.md).
This validates every definition and retains separate initial, transition and
invariant relations. Ordered redefinitions remain separate, and subsystem
bindings retain the definition visible at their source command.

<!-- implicit-constraints:
  absent :input/:output/:local => the corresponding interface is empty, not inherited
  absent :init/:trans/:inv => the empty conjunction true
  a selected :current => replaces the complete flattened initial predicate
  each selected :reachable => a separate eventuality, conjoined with the others
  finite n-semantics => formulas at position n may read primed variables at state n+1
  each subsystem instance => fresh locals; interfaces are identified positionally
  top-level free constants/functions/sorts => one rigid interpretation along a trace
-->

MoXI retains SMT-LIB terms but changes the command and model semantics. A successful
SMT parse is therefore insufficient: `define-system`, primed variables, query selection,
hierarchical composition, and rigid symbols determine which traces satisfy the source.

## 1. Source Institution

For one system, the source signature contains rigid theory symbols and disjoint input,
output, and local state signatures. Its model is

```text
S = (IS[i,o,l], TS[i,o,l,i',o',l'])
```

where `:inv P` contributes `P` to `TS`. Missing `:init`, `:trans`, or `:inv` means
`true`; there is no implicit frame equation. A check-system interface must have exactly
the system's arity and sorts. Its different names are positional aliases, not new variables.

A finite query without fairness denotes

```text
(C or IS) and always TS and always assumptions
and eventually R1 and ... and eventually Rm.
```

`C` is the selected `:current`, if any. Each reachability condition is an independent
eventuality and may have a different witness position. Queries containing fairness use
infinite LTL semantics and are restricted to bounded lassos by this translator.

The assumption profile is SMT-LIB's total-function, theory-arithmetic semantics plus:

- a trailing prime denotes the next valuation, including `|quoted name|'` and the
  reference tool's `|quoted name'|` spelling;
- top-level free sorts, constants, and functions are rigid, not time-indexed inputs;
- enum constructors and expanded `define-fun` bodies retain their SMT meaning;
- attributes are semantic, while malformed commands are static errors.

## 2. Translation Construction

For selected query `q` and bound `n`, the adapter is `(Phi, A, alpha_n, beta, h)`.

`Phi` preserves global sorts, datatypes, rigid constants, and static functions. It flattens
the selected acyclic subsystem hierarchy, identifies child inputs/outputs with parent
arguments, gives every instance fresh locals, and creates state copies `x@0..x@(n+1)`.
The extra state is required because a formula at position `n` may mention `x'`.

`A` contains exact interface-sort checks and datatype declarations. It contains no frame
default. Child `init`, `trans`, and `inv` relations are conjoined with their parent's.

For flattened initial relation `I`, transition relation `T`, assumptions `Aj`, and selected
reachability conditions `Rr`:

```text
alpha_n(q) = I@0
  and AND(k=0..n, T@k)
  and AND(j, k=0..n, Aj@k)
  and AND(r, OR(k=0..n, Rr@k)).
```

A selected `:current C` replaces `I@0`. This is exact for the source's bounded
`n`-satisfaction question. Against unbounded reachability it is an under-approximation:
SAT is a real source trace; UNSAT means only that no witness exists at this bound.

`beta` removes step-name encoding and auxiliary instance names, decodes positional aliases,
and returns the finite source trace plus rigid interpretation. There is no objective map
`h`: MoXI queries have no optimization order.

### 2.1 Fairness through bounded lassos

For at least one selected fairness condition, add a disjunction over loop starts
`l = 0..n`. Each alternative conjoins equality of **every flattened state
component**, including inputs and locals, between positions `n+1` and `l`, and
`OR(k=l..n, F_j@k)` for **each** selected fairness condition. The loop is nonempty.
Repeating `l..n` yields an infinite source trace: the existing transition,
invariant and assumption constraints cover each repeated edge, including primed
inputs. Reachability can be witnessed in the finite prefix. Fairness cannot.
Rigid global symbols retain one interpretation throughout.

This is `bmc-fair-lasso`, with the existing `BMC_DEPTH` bound and an
under-approximation report. SAT witnesses infinite behavior. UNSAT excludes only
these bounded lassos; even unbounded lasso search is incomplete for general
infinite-state systems (an integer that increases forever need not repeat).
The encoding does not claim a serializer for source-level lasso witnesses.

`test/python/test_moxi_fairness.py` compares all sixteen Boolean transition
graphs, two initial states and three fairness requirements (96 cases) against an
independent reachable-cycle oracle. Additional tests distinguish recurring
fairness from prefix reachability, check primed inputs and document the
nonperiodic integer boundary. The source semantics and lasso witness format
are given in Rozier et al., Sections 3.2–3.3 (reference 1).

## 3. Query and Result Boundaries

One `ConstraintModel` represents one question. Multiple `:query` attributes can be handled
with `query=<name>`; multiple check commands additionally require `check_index=<n>`:

```python
import somtparser as sp

result = sp.translate("model.moxi", language="moxi", profile="bmc",
                    options={"bmc_depth": "20", "check_index": "1", "query": "q2"})
assert result.exit_code == 0, result.diagnostics
```

The translator validates all condition/query references before selecting one. It never
merges queries. Queries inside the same `:queries` attribute must share one interpretation
of global free symbols. A grouped query with such symbols is refused because independently
solving one member would weaken that coupling. A future multi-result model must carry the
shared interpretation and a separate trace/verdict for every member.

## 4. Validation and Remaining Work

The frontend structurally reads commands and S-expressions, including nested sorts,
strings, quoted symbols, comments, macros, enums, rigid declarations, and
parametric algebraic datatypes (`declare-datatype`/`declare-datatypes`, passed
through to the engine, which carries `par` parameters). The standard constructor
list has its own parentheses. A nullary constructor can be explicitly typed,
for example `(as Absent (Event Real))`; the engine also infers this instance from
a typed sibling in equality, `distinct`, or the two branches of `ite`. Separate
occurrences can have different instances. Explicit incompatible types remain errors.

The optional reader setting `flat_datatype_constructors=true` additionally reads
`(par (X) (Absent) (Present (val X)))` as
`(par (X) ((Absent) (Present (val X))))`. It only supplies the constructor-list
boundary, never missing operands, types, or constraints. It handles both
`declare-datatype` and the datatype bodies in `declare-datatypes`; standard syntax
is unchanged. Values other than `true` and `false` are errors, and enabling it
conflicts with strict parsing. The default still rejects the flattened spelling.
The normalization appears in query reports or the module's `source_rewrites`
interface entries, including original/normalized declaration and source location.

```python
result = sp.translate("languages/moxi/instances/upstream/QF_LRA_LossyIntChannelX.moxi",
                    module=True, options={"flat_datatype_constructors": "true"})
assert result.exit_code == 0, result.diagnostics
```

This is an explicit dialect for that unchanged upstream source, not a claim that
its original spelling is standard MoXI. Module import retains both ordered
definitions of `LossyRealChannel` and all six relations without inventing a query.
`scripts/audit-moxi-datatype-reader.py` compares the exported functions against
independently specified typed relations with Z3 and cvc5.

The dialect is defined by a partial normalization `N`: complete flattened
constructor sequences become grouped sequences; every other command is passed
through. The standard reader then checks the normalized program. Its semantics
is explicitly `Models_flat(P) = Models_standard(N(P))`. Thus the translation
claim applies to the selected dialect, and carries the same constructor names,
selector sorts, relations, and state signatures. No equivalence claim is made
for a string that has no meaning under the standard grammar. The recorded
rewrite makes this source-language choice inspectable by experiment consumers.

The frontend rejects unknown commands, duplicate query definitions, illegal primes, cyclic
systems, interface mismatches, invalid subsystem wiring, malformed
bounds/selectors, and queries that would require a shared
multi-result interpretation.

Tests in `test/languages/test_moxi*.cpp` cover all rules above. The official
`moxi-mc-flow` corpus exercises rigid constants, both quoted-prime forms, enums, macros,
arrays, subsystem composition, and multiple-query forms. Remaining semantic work is:

- a result IR for grouped queries sharing rigid interpretations;
- response/witness serialization and source-level trace validation.

## 5. References

1. K. Y. Rozier et al., *MoXI: An Intermediate Language for Symbolic Model Checking*,
   Sections 2-3: <https://ahmed-irfan.github.io/papers/spin24.pdf>
2. Official parser, translator, and test corpus:
   <https://github.com/ModelChecker/moxi-mc-flow>
3. SMT-LIB language specifications: <https://smt-lib.org/language.shtml>
