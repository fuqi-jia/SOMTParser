# FlatZinc — MiniZinc's solver-input language

**Date**: 2026-08-25
**Status**: **implemented** (`languages/flatzinc/`, `test/languages/test_flatzinc.cpp`).
Written document-first: every obligation in the block below predates the code.

[Typed module import](../module-import.md) retains declared external predicate
calls, typed arguments and callback annotations alongside known constraints.
An unresolved call remains a dependency and cannot become a closed SMT query.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster A, §3.2 (cost **1.3×**), §4.

<!-- proposed-hir: Op::IFF, ExprKind::ARRAY_ACCESS -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

**Headline result of the audit in §4**: FlatZinc is the cheapest cluster-A language to
*parse* and the most expensive to *interpret honestly*, and those are not the same
sentence. Its grammar is trivial — flat, typed, no nesting, no user functions — but every
file is the **output of somebody else's encoder**. `libminizinc` has already chosen how to
decompose `alldifferent`, how to reify, and how to introduce auxiliary variables. A
FlatZinc→SMT measurement therefore measures *libminizinc's flattening composed with our
encoding*, and reporting it as "MiniZinc translated to SMT" would attribute the CP
toolchain's decisions to this project (§4.1).

The second finding is that FlatZinc inherits MiniZinc's `div`/`mod` convention verbatim
(§4.2), so `minizinc.md` §4.1's trap applies here **without the mitigating factor** that a
MiniZinc frontend at least sees the source: in FlatZinc the operation arrives as
`int_div(a, b, c)`, a predicate call with an innocuous name.


<!-- implicit-constraints:
  array_int_element(i, as, x) => the index constraint 1 <= i <= |as| must also be asserted; without it the ITE chain's final else silently defines as[i] for out-of-range i (§4.3)
  a variable declared with a domain (`var 1..5: x`) => VarDecl bounds; FlatZinc always writes the domain, so this is materialisation rather than inference (§2.2)
  bool2int(b, i) => i is constrained to {0,1} as well as to equal the coercion (§2.3)
  an unrecognised builtin predicate => E_UNSUPPORTED_CONSTRUCT, never a skipped constraint; skipping drops a constraint and weakens the model (§4.5)
-->
---

## 1. What the format is

FlatZinc is the language `libminizinc` emits and a CP solver reads. A `.fzn` file is a
MiniZinc model after *flattening*: types resolved, parameters substituted, comprehensions
expanded, user predicates inlined, global constraints either passed through (if the solver
declares support) or decomposed, and every remaining constraint reduced to a call to a
builtin predicate over variables and literals.

The relationship to `minizinc.md` decides what this project measures:

| Translating | Who chose the encoding | What a result row means |
|---|---|---|
| MiniZinc source | this project | "SMT solves this model, encoded this way" |
| FlatZinc | `libminizinc`, then this project | "SMT solves libminizinc's flattening of this model" |

Neither is wrong. Only the second is easy to report as the first by accident.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| FlatZinc specification, a chapter of the MiniZinc Handbook | **MiniZinc 2.10.0 / FlatZinc 1.6**, checked 2026-08-25 | <https://docs.minizinc.dev/en/stable/fzn-spec.html> |
| Official FlatZinc builtin catalogue | tracks MiniZinc 2.10.0, checked 2026-08-25 | <https://docs.minizinc.dev/en/stable/lib-flatzinc.html> |
| MiniZinc Challenge (the corpus, as `.fzn`) | annual | <https://www.minizinc.org/challenge/> |

The specification is good, and unlike DIMACS (`dimacs-cnf.md` §1) it is normative rather
than "suggested". But it is versioned with MiniZinc, and the **builtin predicate set grows
between releases**. A frontend pinned to no version will meet predicates it has never heard
of; §4.5 says what to do then.

### Reference implementation and corpus

`libminizinc`'s flattener produces the files; Gecode, Chuffed and OR-Tools consume them.
Challenge instances are distributed as MiniZinc models plus data, so obtaining a `.fzn`
corpus means running the flattener — which is itself a version-pinning obligation, since a
different `libminizinc` produces a different `.fzn` from the same model. **Repository URLs,
licences and versions not re-confirmed in this pass**, the same open item
`docs/languages-scoping.md` §1.2 records.

---

## 2. Semantics — what a file means

### 2.1 Structure

A `.fzn` file is, in order: predicate declarations, parameter declarations, variable
declarations, constraint items, and exactly one solve item.

```
predicate all_different_int(array [int] of var int: x);
int: n = 4;
array [1..4] of var 1..4: q :: output_array([1..4]);
var bool: b :: var_is_introduced :: is_defined_var;
constraint int_lin_le([1, -1], [q[1], q[2]], -1);
constraint all_different_int(q);
constraint int_lin_eq_reif([1, 1], [q[1], q[2]], 5, b);
solve :: int_search(q, first_fail, indomain_min, complete) satisfy;
```

Everything is flat: no nesting, no arithmetic expressions, no user-defined predicates with
bodies. An expression like `x + y <= 5` has become `int_lin_le([1,1], [x,y], 5)`.

### 2.2 Types

`bool`, `int`, `float`, fixed `set of int` parameters, finitely bounded decision sets,
and one-dimensional arrays of those. A variable declaration must use
`var set of l..u` or `var set of {...}`; unbounded `var set of int` is admitted only in a
predicate signature, not as an ordinary decision-variable declaration. Multi-dimensional
MiniZinc arrays are flattened to 1-D with computed indices, which is the format's own
answer to a question `xcsp3.md` §4 has to solve differently.

Array index sets are always `1..n`. That is a real simplification over MiniZinc, and one of
the two reasons `docs/languages-scoping.md` §3.2 costs FlatZinc at 1.3× rather than
MiniZinc's full cost.

### 2.3 Builtin predicates

The catalogue is the language. Grouped by what a translation has to do with them:

| Group | Examples | To SMT |
|---|---|---|
| Linear | `int_lin_eq`, `int_lin_le`, `int_lin_ne`, `float_lin_*` | direct: `Σ aᵢ·xᵢ ⋈ c` |
| Arithmetic | `int_plus`, `int_minus`, `int_times`, `int_abs`, `int_min`, `int_max` | direct, given `Op::ABS` |
| **Integer division** | `int_div`, `int_mod` | **§4.2 — not direct** |
| Comparison | `int_eq`, `int_le`, `int_lt`, `int_ne` and `bool_*`/`float_*` siblings | direct |
| Boolean | `bool_and`, `bool_or`, `bool_not`, `bool_xor`, `bool_clause` | direct |
| Coercion | `bool2int`, `int2float` | `ITE(b, 1, 0)`; the float one needs `SortKind::REAL` |
| Element | `array_int_element`, `array_var_int_element`, `array_bool_element` | §4.3 |
| Set | `set_in`, `set_card`, `set_subset`, `set_union` | `SortKind::SET` and the finite-set operators landed 2026-08-12 |
| Global | `all_different_int`, `cumulative`, `table_int`, `regular`, `circuit`, … | §4.4 |
| **Reified** | any of the above with a `_reif` suffix, plus `_imp` half-reified variants | §4.6 |

`docs/related-work-round2.md` §3 counts XCSP3's catalogue at ~20 constraint families;
FlatZinc's builtin list is comparable in size and, crucially, *open* — a solver may declare
support for additional predicates.

The implemented exact catalogue also includes `array_bool_and/or/xor`,
`array_int_minimum/maximum`, `fzn_count_eq(_par)`, `array_int_lt/lq`, finite
`gecode_table_int`, and offset-based `gecode_int_element`. These are relations, not
function-name rewrites: empty Boolean folds use their logical identities, tables are
row-major disjunctions, and element encodings carry an explicit index-domain guard.

`gecode_table_int` requires a parameter integer table, including for empty
arrays. Equal table contents and tuple width share one auxiliary HIR function;
each call supplies its own tuple, preserving aliases and reification. The
function body also shares column/value tests across rows. This avoids repeated
front-end expansion while retaining the complete extensional relation.

The MiniZinc 2.9.4 / Gecode challenge spellings additionally supported are
`gecode_bool_element`, `gecode_int_element2d`, `gecode_global_cardinality`,
`fzn_global_cardinality_low_up_closed`, `gecode_bin_packing_load`, `fzn_nvalue`,
`gecode_circuit`, and `fzn_increasing_int`. The open cardinality relation permits
values outside `cover`; its closed counterpart requires every value to belong to
`cover`. Repeated cover labels retain every count equality or bound. Integer
histograms and visited-value arrays share their immutable prefixes, giving linear
HIR size in the input cells and cover/load cells. The increasing relation is
non-strict.

The two-dimensional element adapter preserves contiguous source row/column index
sets and row-major flattening. Both index dimensions remain guarded, including
under reification. Sparse index sets are diagnosed. Integer element offsets use
exact integer arithmetic. Gecode circuit permits a singleton self-loop; this is
handled before invoking the shared HIR circuit encoding, whose singleton convention
differs. Its offset must be nonnegative and its successor array nonempty.

These contracts follow the [MiniZinc 2.9.4 Gecode bridge](https://github.com/MiniZinc/libminizinc/blob/2.9.4/solvers/gecode/gecode_constraints.cpp)
and Gecode's [cardinality implementation](https://github.com/Gecode/gecode/blob/release-6.3.0/gecode/int/gcc.cpp)
and [singleton circuit implementation](https://github.com/Gecode/gecode/blob/release-6.3.0/gecode/int/circuit/val.hpp).

`gecode_maximum_arg_int_offset` returns the first maximizing array position
plus the parameter offset; equal maxima keep the smallest position. The array
must be nonempty, as required by Gecode. Exact integer offsets are preserved.
`gecode_regular` uses the parameter Q-by-S row-major transition table, start
state in `1..Q`, and accepting subset of `1..Q`. A zero transition or an input
outside `1..S` reaches the absorbing rejecting state. The empty word is accepted
exactly when the initial state is accepting. Q and S must be positive; malformed
parameter tables and state sets are diagnosed. The encoding uses a total nested
array table, so missing transitions remain rejecting under negative polarity.
The existing `_reif`/`_imp` adapter applies to these same Boolean relations; this
is an adapter extension, not a claim that Gecode exports those suffix names.
These two contracts follow the pinned MiniZinc 2.9.4 Gecode library and Gecode
6.3.0 [FlatZinc registration](https://github.com/Gecode/gecode/blob/release-6.3.0/gecode/flatzinc/registry.cpp).

### 2.4 Annotations

Annotations carry information the flattener wants to pass on:

| Annotation | Meaning | Fidelity impact |
|---|---|---|
| `::output_var`, `::output_array` | this variable is part of the answer | **not none** — see below |
| `::var_is_introduced` | the flattener created this variable, the user did not | none |
| `::is_defined_var`, `::defines_var(x)` | this variable is functionally determined by that constraint | none, but useful |
| `::int_search(...)`, `::seq_search(...)` | search strategy | none (`minizinc.md` §2.5) |

`output_var`/`output_array` are the exception and deserve care. They define the *solution
vocabulary*: a FlatZinc answer prints only annotated variables, because the rest are
flattening artefacts. A differential test that compares models rather than verdicts must
compare exactly this projection — comparing all variables would report a disagreement every
time the two toolchains introduced different auxiliaries. This is the same trap
`dimacs-cnf.md` §3 records for unused DIMACS variables, in a sharper form: here the extra
variables are guaranteed to exist.

### 2.5 The solve item

`solve satisfy;`, `solve minimize x;` or `solve maximize x;` — and in FlatZinc the objective
is **always a single variable**, never an expression, because flattening introduced one.
The HIR stores this scalar objective as one `ExprPtr` term
(`Hir::Objective` in `include/somtparser/hir/hir.h`). The shared emitter prints it through
the lowered target node (`termText` in `src/lowering/omt_emitter.cpp`), including exact
numeric spellings. It also renders compound HIR objective terms used by other
frontends; FlatZinc's own solve-item restrictions remain a frontend contract.


---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| `var bool: b` | `VarDecl{name, Sort::boolean()}` (`include/somtparser/hir/hir.h`) | none | `exact()` |
| `var int: x`, `var l..u: x` | `VarDecl` with optional `lower_bound`/`upper_bound` | none | `exact()` |
| `var float: f` | `VarDecl{Sort::real()}` with `ExprKind::LIT_REAL` for its constants (landed 2026-08-12) | none | `exact()` |
| `int: n = 4` (parameter) | substituted; no HIR node | none | `exact()` |
| `array [1..n] of var int` | — | `SortKind::ARRAY` | — |
| `int_lin_eq([a…],[x…],c)` | `EQ(ADD(MUL(a₁,x₁), …), c)` | none | `exact()` |
| `int_lin_le`, `int_lin_ne` | `LE(…)`, `NOT(EQ(…))` | none | `exact()` |
| `int_plus/minus/times` | `Op::ADD` / `SUB` / `MUL` | none | `exact()` |
| `int_abs(x, y)` | `EQ(y, ITE(x ≥ 0, x, NEG x))` | `Op::ABS` or `Op::ITE` | `exact()` |
| `int_div`, `int_mod` | **§4.2** | `Op::DIV_TRUNC`, `Op::MOD_TRUNC` | `exact()` if corrected |
| `int_eq/le/lt/ne` | `Op::EQ` / `LE` / `LT` / `NOT(EQ)` | none | `exact()` |
| `bool_and/or/not` | `Op::AND` / `OR` / `NOT` | none | `exact()` |
| `bool_xor(a,b,r)` | `EQ(r, NOT(EQ(a,b)))` | none | `exact()` |
| `bool_clause(pos, neg)` | `OR(pos… , NOT(neg)…)` | needs arrays to read the two lists | `exact()` |
| `bool2int(b, i)` | `EQ(i, ITE(b, 1, 0))` | `Op::ITE` | `exact()` |
| `array_*_element` | §4.3 | `ExprKind::ARRAY_ACCESS` | `exact()` |
| `set_*` | §4.4 | none — `SortKind::SET` landed 2026-08-12 | varies |
| global predicates | §4.4 | cluster A's shared work | varies |
| `_reif` / `_imp` variants | §4.6 | none — the point of §4.6 | `exact()` |
| `::output_var` / `::output_array` | recorded, not lowered | none | `exact()`, but see §2.4 |
| search annotations | dropped | none | `exact()` |
| `solve minimize x` | `Objective{MINIMIZE, mkIdent(x)}` | none | `exact()` |

---

## 4. Semantic gaps and encoding choices

### 4.1 The measurement question, which is not an encoding question

This is the finding that governs how a FlatZinc result may be reported, and it is not
visible in the fidelity lattice at all — `Fidelity` describes the relation between the HIR
model and the SMT script, and by the time we see a `.fzn` the interesting transformation
has already happened.

Concretely, `alldifferent` over five variables may arrive as:

- `all_different_int(x)` — a single call, if the flattener was told the solver supports it;
- ten `int_ne` constraints — the pairwise decomposition;
- a `table_int` or a bitmask encoding, under other flattener settings.

Same MiniZinc source, three different `.fzn` files, three different SMT scripts, three
different runtimes. The variation is `libminizinc`'s, not ours.

| Reporting choice | Honest? |
|---|---|
| "MiniZinc, translated to SMT" | **no** — attributes the flattener's decisions to us |
| "FlatZinc (libminizinc `<version>`, `<flags>`), translated to SMT" | yes |
| Both arms, compared | yes, and the more interesting experiment: it measures what the flattener's decomposition costs relative to ours |

The last row is worth stating as a positive: running MiniZinc→SMT and MiniZinc→FlatZinc→SMT
side by side isolates the flattener's contribution, which is exactly the kind of question
`docs/languages-scoping.md` §6's second filter exists to keep clear. Record the flattener
version and flags in `TranslationReport`'s provenance — `Uir::Provenance` already carries a
`language_version`, and for FlatZinc that must mean *the flattener's* version, not the
format's.

### 4.2 `int_div` and `int_mod` inherit MiniZinc's convention

FlatZinc's `int_div` and `int_mod` mean what MiniZinc's `div` and `mod` mean: truncation
toward zero, remainder taking the sign of the dividend. SMT-LIB's `Ints` theory is
Euclidean. `minizinc.md` §4.1 has the table and the correction; everything there applies
unchanged.

Two things make it *worse* here:

- **The name gives nothing away.** In MiniZinc source the operator is spelled `div`, which
  at least invites the question. `int_div(a, b, c)` looks like a constraint over three
  variables, and a frontend author reading the builtin list has no reason to stop.
- **The engine's operator table maps `div` to `NT_DIV_INT`**
  (`include/somtparser/core/kind.h:53`) and `mod` to `NT_MOD` (`:221`), so emitting the
  obvious thing yields the other semantics silently.

Checking that claim while writing `minizinc.md` found that the engine's own folding matched
neither convention and violated the identity defining both; that is fixed
(`test/regression/test_int_div_mod_semantics.cpp`), and the engine is now correct SMT-LIB.
Which means a FlatZinc frontend that emits `div` now gets *correct Euclidean* semantics for
a *truncating* source operator — a clean mismatch rather than a mess, but still a wrong
answer.

**Encoding**: as `minizinc.md` §4.1, and the recommendation to name the convention in the
HIR operator (`Op::DIV_TRUNC`) is stronger here for the naming reason above.

### 4.3 `element` is where arrays stop being optional

`array_int_element(i, as, x)` means `as[i] = x` with `as` a parameter array and `i` a
variable index. `array_var_int_element` is the same with a variable array.

| Encoding | Form | Fidelity | Note |
|---|---|---|---|
| Nested `ITE` chain | `x = ite(i=1, a₁, ite(i=2, a₂, …))` | `exact()` | O(n) nodes, no theory needed; the default |
| Disjunction of conjunctions | `⋁ᵢ (i = k ∧ x = aₖ)` | `exact()` | same size, sometimes better for a SAT-based backend |
| SMT array theory | `select(a, i) = x` | `exact()` | needs the array sort and an `ArrayLit` to build `a`; the engine has `NT_SELECT`/`NT_STORE` but the HIR has no array sort |
| Index-domain restriction | bound `i` to the array's range | this is *already implied*; asserting it is not a fidelity loss | required for the `ITE` chain's last branch to be sound |

The last row is the trap: the `ITE` chain's innermost `else` has to be *something*, and
choosing `aₙ` silently defines `as[i]` for out-of-range `i`. FlatZinc's own semantics makes
out-of-range indexing a failure (the MiniZinc relational semantics, `minizinc.md` §4.2), so
the constraint must also assert `1 ≤ i ≤ n` rather than let the chain decide.

### 4.4 Globals and sets: cluster A's shared work

The global predicates arrive as calls, which is *easier* than MiniZinc's library — no
inlining, no type checking, just a name and arguments. The encoding question is identical
and is cluster A's shared decomposition library (`minizinc.md` §4.3), so this document does
not restate it. `xcsp3.md` §4 enumerates the catalogue, because XCSP3 specifies one.

Sets are the exception, because a parameter `set of int` is a fixed value while a decision
set ranges over subsets of a declared finite upper carrier. The SMT representation uses
`(Set Int)` plus an explicit `set.subset` declaration axiom in `A_Sigma`; membership,
subset, equality, cardinality, union, intersection and difference remain exact. The
frontend rejects an ordinary unbounded `var set of int` declaration: accepting it would
both violate the FlatZinc grammar and admit infinite SMT sets that have no source value. As a
compiler extension, a fully initialized `array [1..n] of var set of int` is accepted
when every cell is a finite set literal, a fixed set parameter, or an already
bounded decision-set alias. The initializer must contain exactly `n` cells; it
cannot introduce unbounded set variables. Bounded set arrays constrain every cell,
including literals and parameters, to their declared upper carrier. Output
projection reconstructs fixed cells as constants and reads decision aliases from
the target assignment. `array_set_element` and `array_var_set_element` use
set-valued cells with the same 1-based index guard as scalar element constraints.
Reification and implication apply to the complete guarded relation, so an
out-of-range index makes the underlying relation false. A well-typed empty set
array likewise has the false element relation for every index.
Cardinality retains the declared finite carrier in its term: under the
unconditional declaration axiom, `card(s)` equals `card(s intersect carrier)`.
This also gives the Z3 exporter exact support for sparse, negative, and empty
carriers without treating a reified cardinality equality as an assertion.

### 4.5 Unknown predicates must fail, not be guessed

The builtin set grows between MiniZinc releases, and solvers may declare their own. A
frontend will meet a predicate it does not know.

| Policy | Consequence |
|---|---|
| Ignore the constraint | **Never.** Drops a constraint: the translated problem is weaker, `sound = false`, and it exits 0 |
| Guess from the name | worse — `int_lin_eq_imp` differs from `int_lin_eq_reif` by one letter and one direction of implication |
| Refuse with `E_UNSUPPORTED_CONSTRUCT`, naming the predicate | correct; the name lands in the coverage statistic, which is exactly what `include/somtparser/translation/diagnostic.h` says that bucket is for |

The third is the only defensible one, and it is also the one that makes the coverage table
mean something: `OpCoverage::missing` should carry the predicate names, so the report says
which builtins are unimplemented rather than that "some are".

### 4.6 Reification is free in SMT, and that is worth saying out loud

Every FlatZinc predicate has a reified twin: `int_lin_eq_reif(as, bs, c, b)` constrains `b`
to be true exactly when the linear equation holds. Half-reified `_imp` variants constrain
only one direction.

In CP this is a substantial mechanism — a solver needs a propagator for each reified form.
In SMT it is nothing: a formula *is* a term of sort Bool, so `int_lin_eq_reif(…, b)` is

```
b ⟺ (Σ aᵢ·xᵢ = c)
```

which is `EQ` on two Bools, expressible today (`Op::EQ` over Bool operands is accepted —
`Uir::Hir::typeCheck` allows `=` between two Bools and only rejects mixed sorts). The `_imp`
variants are one implication instead of two.

So the whole `_reif` half of the catalogue costs a frontend one uniform rule and no encoding
choice. This is the clearest case in the batch of the SMT target being *richer* than the
source's target, and it is worth recording because the size of the `_reif` list makes it
look like a cost.

`Op::IFF` would make this direct rather than an `EQ` over Bools; it is on the proposed list
for readability, not necessity.

---

## 4.7 What building it settled

**The fourth obligation governs the design rather than sitting beside it.** The catalogue is
*open* — a solver may declare support for additional predicates — so a frontend meets unknown
names as a matter of course, and there is no version of "handle the catalogue" that finishes.
Refusing by name is therefore the normal path and not the error path, which is why the
coverage figure here is about §2.3's *groups* and not about the language.

**Reification is handled generically**, by stripping `_reif` and equating the base constraint
with the trailing Boolean. One case per reified name would fall behind an open catalogue by
construction.

**Half reification is also generic and directional.** `_imp(args,b)` means
`b => base(args)`, not equivalence and not the reverse implication. The regression test
uses a false base relation so either wrong direction changes the feasible models.

**Variable initializers are declaration axioms.** `var int: x = y` adds `x = y` to
`A_Sigma`; it is not a parameter substitution. The same rule handles fixed set values.
The old reader retained the initializer text but emitted no equality, silently leaving an
output variable unconstrained.

**`all_different_int` is routed through the decomposition pass**, as a `Hir::Global`.

It was expanded pairwise in the frontend until 2026-08-17, on the stated reason that
"`ExprKind::GLOBAL` takes an *array*; a FlatZinc argument is a list of variables". **The
premise was false.** `alldifferent` has two shapes — `alldifferent(array, lo, hi)` and
`alldifferent(t1, …, tn)` — dispatched on the first argument's sort (`src/hir/typecheck.cpp`),
and the list shape exists precisely because `alldifferent([x, y, z])` has no array to point
at. The workaround was scrupulous about its cost, recording in the open-questions log that
the profile axis was unreachable from here; it is worth naming that a *documented* limitation
is still one nobody rechecked, and this one had stopped being true.

The emitted script is unchanged — the pass's list shape builds the same pairwise conjunction —
and two things are different. The decision is now recorded as an `EncodingChoice`, so a report
can distinguish "insensitive to the profile" from "never asked; and the encoding lives in the
pass, so a better decomposition reaches FlatZinc without touching this frontend.

**The ground/quantified axis is still not variable here**, and now for a precise reason rather
than a mistaken one: the list shape is pairwise under *both* styles, because a list of terms
has no index set to quantify over. Making it variable means declaring real HIR arrays for
FlatZinc's variable vectors, which changes every variable reference this frontend emits.
Essence′ is the contrast — it declares real arrays, so it reaches the indexed shape and does
respond to the profile.

**Annotations are dropped, and the test pins that they change nothing** — the same file with
and without `::output_var`, `::var_is_introduced`, `::defines_var` and a search annotation
produces byte-identical output. §2.4's exception, `output_var` defining the solution
vocabulary, matters only to a model-level differential comparison, which is not this layer.

---

## 5. New HIR surface this format forces

FlatZinc needs a **strict subset** of what MiniZinc needs — which is the substance of
`docs/languages-scoping.md` §3.2's "**New HIR feature** (shared with MiniZinc)" note and of
its 1.3× cost.

| Surface | Needed for | Also needed by |
|---|---|---|
| `SortKind::ARRAY` + `ExprKind::ARRAY_ACCESS` | every array declaration, `element`, `bool_clause` | MiniZinc, XCSP3, Essence′ |
| a global-constraint call form | the global predicates | all of cluster A |
| `Op::DIV_TRUNC`, `Op::MOD_TRUNC` | `int_div`, `int_mod` (§4.2) | MiniZinc, Boogie, CryptoLine |
| `Op::ABS` | `int_abs` | MiniZinc |
| ~~`ExprKind::LIT_REAL`~~ **landed 2026-08-12** | `float_*` and `int2float` | LP, MPS, MiniZinc |
| ~~`SortKind::SET`~~ **landed 2026-08-12** | `var set of int` (§4.4) | MiniZinc, Essence′ |

**Not needed, unlike MiniZinc**: comprehensions (expanded by the flattener), user-defined
predicates (inlined), enums (resolved to integers), option types (eliminated), and
multi-dimensional arrays (flattened to 1-D). Every one of those is a real saving and is why
FlatZinc is worth doing *after* MiniZinc rather than instead of it — the shared surface is
built once and FlatZinc uses the cheap half.

**`Op::ITE`** deserves a line: §4.3's element encoding and §2.3's `bool2int` both want it,
and both have workarounds. It is the highest-value non-blocking addition for this language.

---

## 6. Fidelity summary

**Exact — most of the format.** Linear constraints, arithmetic, comparisons, Boolean
operations, coercions, reification in both full and half forms, the objective, and the
`element` constraint given an index-range assertion (§4.3).

**Exact, once the surface exists.** Arrays, `abs`, real literals, and the global
decompositions that are exact (`minizinc.md` §4.3).

**Inherently lossy**:

- Float constraints, if the backend is floating point rather than real — a different
  theory, not a bound.

**Ways to make it lossy by mistake**:

- Emitting SMT-LIB `div`/`mod` for `int_div`/`int_mod` (§4.2). **Silent.**
- Ignoring an unrecognised builtin instead of refusing (§4.5). **Silent, and drops a
  constraint outright.**
- Encoding `element` without asserting the index range, which defines the array outside its
  domain (§4.3).
- Comparing full models rather than the `output_var`/`output_array` projection, which makes
  every auxiliary variable look like a disagreement (§2.4).

**Not a fidelity question at all, and the most important one**: reporting a FlatZinc result
as a MiniZinc result (§4.1). No value of `Fidelity` describes it, because the loss happened
before the file existed.

---

## 7. References

**Language specification**

1. FlatZinc 1.6 specification, MiniZinc Handbook 2.10.0.
   <https://docs.minizinc.dev/en/stable/fzn-spec.html> — checked 2026-08-25; note that
   the flattener's version is what a result must record (§4.1).
2. Official FlatZinc builtin catalogue.
   <https://docs.minizinc.dev/en/stable/lib-flatzinc.html>.
3. SMT-LIB `Ints` theory, for the Euclidean `div`/`mod` semantics §4.2 compares against.
   <https://smtlib.cs.uiowa.edu/theories-Ints.shtml>

**Corpus**

4. MiniZinc Challenge. <https://www.minizinc.org/challenge/> — models plus data; a `.fzn`
   corpus is produced by running the flattener, which pins a version by construction.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster A), §3.2 (1.3×, "shared with MiniZinc"),
   §4 (Plan 2), §6 (the second filter).
6. `docs/languages/minizinc.md` §4.1 (the `div`/`mod` convention and the engine defect it
   uncovered), §4.2 (the relational semantics of partial functions), §4.3 (global
   constraint decomposition), §2.5 (search annotations).
7. `docs/languages/dimacs-cnf.md` §3 (models-versus-verdicts in differential testing).
8. `docs/languages/xcsp3.md` §4 (the global-constraint catalogue, enumerated there).
9. `test/regression/test_int_div_mod_semantics.cpp` (the two laws §4.2 depends on).
10. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
   `include/somtparser/translation/diagnostic.h`, `include/somtparser/core/kind.h`,
   `src/lowering/omt_emitter.cpp`.

### Solve annotations and objectives

Search annotations between `solve` and `satisfy`, `minimize`, or `maximize`
are ignored as search hints. Nested annotation arguments and quoted strings do
not change the selected goal, its direction, or its scalar objective. Empty
solve items are rejected. Quoted annotation arguments on declarations also
preserve a following initializer.

Objective labels are chosen independently of source variable names. Signed integer literals, including a leading `+` and values beyond 64 bits, retain their exact numeric value in constraints and emitted objectives.
