# LP format — linear and mixed-integer programs

**Date**: 2026-08-25
**Status**: **implemented linear subset, 6/9 feature families**
(`languages/lp/`, `test/languages/test_lp.cpp`). Every accepted path is translated
exactly; quadratic expressions, indicators, and SOS are refused explicitly.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster **B**, §3.2 (cost **0.5×**), §4.

<!-- proposed-hir: ExprKind::LIT_RATIONAL -->
<!-- rejected-hir: ExprKind::LIT_BIGINT -->
<!-- Considered and deliberately not built; see docs/languages/opb-wbo.md §4.6.
     The gap it names is closed by a text-backed LIT_INT instead. -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

**Current audit result:** `ExprKind::LIT_REAL` now carries decimal and scientific
coefficients as exact rationals, so the earlier literal gap in §4.1 is closed. The central
remaining semantic obligation is the implicit domain: **an LP variable's default lower
bound is 0, not −∞** (§4.2). The adapter also keeps binary, integrality,
semi-continuous/semi-integer, range, and objective-offset semantics explicit.

<!-- implicit-constraints:
  a variable with no Bounds entry => VarDecl::lower_bound = 0; LP variables are non-negative unless declared otherwise, and omitting this yields a strictly weaker model that exits 0 and reports exact (§2.2, §4.2)
  a Binary section variable => integer with intrinsic [0,1], intersected with any explicit Bounds restriction (§2.3)
  a Semi-Continuous variable => the disjunction x = 0 OR l <= x <= u, not the interval [0,u] (§2.3, §4.4)
  `<` in a constraint => means <=; linear programming has no strict inequality, so emitting Op::LT is a different model (§2.4)
  a decimal/scientific token => an exact rational value, not a binary floating-point approximation (§4.1)
-->
---

## 1. What the format is

The LP format is a human-readable, line-oriented, algebraic way of writing a linear or
mixed-integer program: an objective, a list of constraints, variable bounds, and integrality
declarations. It is the format people hand-write and paste into issue reports, as opposed to
MPS (`mps.md`), which is the format tools exchange.

### There is no standard

This is the format's defining property and the first thing a frontend must confront. LP is
defined by **vendor documentation**, and the vendors differ:

| Dialect | Documented by | Notable differences |
|---|---|---|
| CPLEX LP | IBM CPLEX file-format reference | the original; `\` comments, section keywords |
| Gurobi LP | Gurobi reference manual | general constraints, differing name rules |
| GLPK CPLEX-LP | GLPK reference | a documented subset |

The adapter pins its accepted syntax as CPLEX LP in `Language::version()`; "LP format"
without a dialect is not a well-defined input language. This is a weaker basis than MiniZinc's
specification chapter (`minizinc.md` §1) and closer to DIMACS's "suggested format"
(`dimacs-cnf.md` §1) — but unlike DIMACS, the divergences are semantic, not just lexical
(§4.6).

### Corpus

LP files circulate widely, but the *ranked, versioned* corpus for this problem class is
**MIPLIB 2017**, which is distributed in MPS. `mps.md` is therefore the corpus-bearing
document of the pair, and an LP frontend's realistic role is convenience input rather than
an experiment arm of its own. Stated here so the two documents are not read as describing
two independent measurement arms: **they describe one arm with two front doors.**

---

## 2. Semantics — what a file means

### 2.1 Structure

```
\ a comment
Maximize
 obj: 0.5 x + 2 y + 3 z
Subject To
 c1: x + y + z <= 10
 c2: -5 <= x - y <= 5
 c3: 3 x + 2 y >= 4
Bounds
 0 <= x <= 40
 y free
General
 z
Binary
 w
End
```

Sections, in order: an objective (`Maximize` / `Minimize`, or `Maximise` / `Minimise`), then
`Subject To` (`s.t.`, `st`), then any of `Bounds`, `General` / `Integer`, `Binary`,
`Semi-Continuous`, `SOS`, and finally `End`. Keywords are case-insensitive. Everything after
`\` on a line is a comment.

### 2.2 Variables, and the bound that is not written down

**A variable's default domain is `[0, +∞)`.**

This is not a convention a reader may take or leave. It is the LP format's semantics, and it
comes from linear programming's own tradition, where variables are non-negative unless
declared otherwise. A variable that appears only in the objective and constraints, with no
`Bounds` entry, is *still* constrained to be non-negative.

`Bounds` overrides it: `-10 <= x <= 10`, `x >= 5`, `x <= 3` (which leaves the lower bound at
0), `x free` (−∞ to +∞), `x = 7`.

§4.2 is about what happens when this is missed.

### 2.3 Variable classes

| Section | Domain |
|---|---|
| *(default)* | continuous, `[0, +∞)` unless `Bounds` says otherwise |
| `General` / `Integer` | integer, same default bounds |
| `Binary` | integer in `{0, 1}`; an explicit `Bounds` entry further restricts that carrier |
| `Semi-Continuous` | `x = 0` **or** `l ≤ x ≤ u` — a disjunction, not an interval (§4.4) |

### 2.4 Constraints

`name: expression ⋈ rhs` with `⋈ ∈ {<=, =<, <, >=, =>, >, =}`. Note that `<` and `<=` mean
the **same thing** in LP: linear programming has no strict inequality, and a `<` is read as
`≤`. A frontend that emits `Op::LT` for `<` produces a different model.

**Range constraints** come in two spellings: `-5 <= x - y <= 5` on one line, or a named row
with a separate range (the MPS `RANGES` mechanism, `mps.md` §2.4). Both mean a two-sided
constraint and lower to a conjunction of two comparisons.

### 2.5 Objective

One linear (or quadratic, §4.5) expression, minimised or maximised. A constant term is
allowed and is common. An *empty* objective is legal and means pure feasibility.

### 2.6 What a solution is

An assignment to every variable satisfying every constraint and every bound, optimal for the
objective. Because most variables are continuous, this is an **LRA/LIRA** question rather
than an integer one, which is the interesting fact for the experiment: LP is the batch's
main source of *real-arithmetic* instances, and the HIR cannot express a real constant
(§4.1). The two facts are the same fact.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| continuous variable | `VarDecl{name, Sort::real()}` + **the implicit `≥ 0`** (§4.2) | none for the decl | `exact()` |
| `General` variable | `VarDecl{name, Sort::integer()}` + implicit `≥ 0` | none | `exact()` |
| `Binary` variable | `VarDecl{integer(), lower_bound = 0, upper_bound = 1}` | none | `exact()` |
| `Semi-Continuous` | §4.4 | `Op::ITE` or a disjunction | `exact()` |
| **integer coefficient** | `mkInt(v)` | none | `exact()` |
| **decimal coefficient** | `ExprKind::LIT_REAL`, exact (landed 2026-08-12) | none | **§4.1** |
| `a x + b y` | `Op::ADD` over `Op::MUL` | none, given the literals | `exact()` |
| `<=`, `=<`, `<` | `Op::LE` — all three (§2.4) | none | `exact()` |
| `>=`, `=>`, `>` | `Op::GE` | none | `exact()` |
| `=` | `Op::EQ` | none | `exact()` |
| range `l <= e <= u` | `AND(GE(e,l), LE(e,u))` | none | `exact()` |
| `Bounds` entry | `VarDecl::lower_bound` / `upper_bound` | none | `exact()` |
| `x free` | both bounds null | none | `exact()` |
| objective | `Objective{MINIMIZE\|MAXIMIZE, term}` (`include/somtparser/hir/hir.h`) | none | `exact()`, but see §4.3 |
| objective constant term | part of the term | none | `exact()` |
| `SOS1` / `SOS2` | §4.4 | — | `exact()` |
| quadratic term | §4.5 | none (`Op::MUL` is enough) — but it makes the model non-linear | `exact()` |
| `\` comment | dropped | none | `exact()` |

---

## 4. Semantic gaps and encoding choices

### 4.1 The correction to cluster B: there is no real literal

`docs/languages-scoping.md` §3.1's cluster B is "None (fits `ConstraintModel` today)" and
lists LP among five members. For LP the claim fails on the first line of any real file.

**The gap, stated exactly.** `Hir::Expr` (`include/somtparser/hir/hir.h`) has
`bool bool_value` and `long long int_value` and nothing else numeric.
`ExprKind` (`:43`) has `LIT_BOOL` and `LIT_INT`. `mkInt` takes a `long long` (`:67`). There
is no constructor, no field and no kind for a non-integer constant.

Note that this is a limitation of the **HIR**, not of the engine: `Parser::mkConstReal`
exists in three overloads, including one taking a string
(`include/somtparser/frontend/parser.h:1125`), so the target can represent the value
perfectly. The IR in the middle cannot. That is the same shape as every other gap in this
batch — the HIR is poorer than what it lowers onto.

**The rescue, and why it is not enough.** LP coefficients are finite decimals, hence
rationals, so a constraint can be scaled by the least common multiple of its denominators:

```
0.5 x + 1.25 y <= 3.75        ×4        2 x + 5 y <= 15
```

This is exact — multiplying both sides of a linear inequality by a positive constant
preserves the solution set — and it needs no new HIR at all. It fails for three reasons,
in increasing order of seriousness:

1. **The objective's value changes.** Scaling the objective row by *k* multiplies the
   optimum by *k*. Recoverable (divide back), but it must be *recorded*, or the reported
   optimum is wrong by a factor nobody wrote down.
2. **Coefficients grow.** The LCM of the denominators of a row with `0.001` and `1/7`-ish
   decimals is large, and the scaled integers overflow `long long` quickly. This is exactly
   `opb-wbo.md` §4's `ExprKind::LIT_BIGINT` finding arriving from a different direction:
   the two gaps compose, and fixing only one leaves the format unrepresentable.
3. **It changes the theory.** An LP over rationals scaled to integers is still an LRA
   problem if the *variables* are continuous — scaling the coefficients does not make `x`
   an integer. So the scaling buys literal representability, not a change of logic, and the
   variables still need `SortKind::REAL`, which the HIR does have.

**Recommendation**: `ExprKind::LIT_REAL` holding a *rational* (numerator/denominator as
arbitrary-precision integers), not a `double`. A `double` cannot represent `0.1` and would
make the translation lossy at the literal level — a loss with no honest `Fidelity` value,
because it is not an approximation of the model but a misreading of the file.

**The scoping document should be corrected**: cluster B's membership is DIMACS CNF alone
without qualification, WCNF with the `weight`-is-a-`double` footnote its own document
records, and LP, MPS and OPB/WBO each needing a literal extension.

### 4.2 The default lower bound of 0 — the silent wrong answer

A variable with no `Bounds` entry is constrained to `[0, +∞)` (§2.2). A translation that
emits

```
(declare-fun x () Real)
```

and nothing else has declared a variable over **all** reals. Every negative assignment is
now legal that was not legal before.

| | original | naive translation |
|---|---|---|
| solution set | `{x ≥ 0, …}` | `{x ∈ ℝ, …}` ⊋ original |
| `sound` (translated SAT ⟹ original SAT) | — | **false** |
| `complete` (original SAT ⟹ translated SAT) | — | true |
| what a solver reports | UNSAT for an infeasible LP | possibly SAT, with a negative witness |
| what the pipeline reports | — | success, `Fidelity::exact()` |

This is the most likely first bug in an LP frontend and it is invisible to every check in
the pipeline: the file parses, the model type-checks, the script round-trips, and the answer
is wrong in the direction that produces a confident SAT.

**The fix is one line and must be tested for, not assumed**: every variable without an
explicit lower bound gets `VarDecl::lower_bound = 0`. An `instances/reject/` or
`instances/ok/` fixture whose LP is infeasible **only** because of the implicit bound is the
right regression test — one that would pass if the bound were dropped is not a test of this
at all, which is the `docs/known-defects-2026-08-11.md` §4 lesson applied in advance.

The same rule applies to MPS (`mps.md` §4.2), where it is joined by a second bound trap.

### 4.3 Maximisation, and what `preserves_optimum` means here

`Hir::ObjKind` has `MAXIMIZE` (`include/somtparser/hir/hir.h`) and the emitter renders
`(maximize …)` for the Z3 and OptiMathSAT dialects
(`src/lowering/omt_emitter.cpp`, `emitRenderedObjectives`), so LP's maximization needs no negation trick. Good —
because the trick (`minimise −f`) is exact for the *argument* but changes the reported
*value*, and doing it silently would be the same class of unrecorded transformation as
§4.1's scaling.

`Fidelity::preserves_optimum` is meaningful for this language, unlike the pure-satisfaction
formats where it is vacuously true (`dimacs-cnf.md` §2.2). Any encoding that scales,
negates or shifts the objective must either preserve the value or record that it did not.

### 4.4 Semi-continuous variables and SOS sets are disjunctions

Both are constructs a MIP solver handles natively and SMT expresses directly.

| Construct | Meaning | Encoding | Fidelity |
|---|---|---|---|
| `Semi-Continuous x, l, u` | `x = 0 ∨ l ≤ x ≤ u` | that disjunction, verbatim | `exact()` |
| `SOS1` over `x₁…xₙ` | at most one is non-zero | `Σ ITE(xᵢ ≠ 0, 1, 0) ≤ 1`, or pairwise `xᵢ = 0 ∨ xⱼ = 0` | `exact()` |
| `SOS2` over `x₁…xₙ` | at most two non-zero, and adjacent | as SOS1 plus an adjacency disjunction | `exact()` |
| indicator `b = 1 -> e <= r` | implication | `Op::IMPLIES`, or `OR(NOT b, …)` | `exact()` |

The `big-M` reformulation a MIP practitioner would reach for is **not** needed and should
not be used: it requires choosing an `M`, and a too-small `M` silently cuts off solutions
(`underApprox`) while a too-large one is numerically bad for no benefit. SMT expresses the
disjunction directly, which is one of the clearer cases where the target is a better fit
than the source's usual solver.

### 4.5 Quadratic terms take the model out of linear arithmetic

**Implemented 2026-09-20.** LP allows quadratic objectives and constraints
(`[ x^2 + 2 x * y ] / 2`). The HIR expresses them with `Op::MUL` and needs nothing new, and
`ConstraintModel::features()` already detects them: `hasNonlinearMul` reports
`feat::nonlinear()` when a product has two non-constant factors
(`src/hir/hir.cpp`).

The divisor is **read from the text, not assumed from the position**. CPLEX conventionally
writes an objective's form over two and a quadratic *constraint* with no divisor at all, and
`qcqp.lp` carries one of each in a single file — so assuming the `/2` would halve every
constraint coefficient and ignoring it would double every objective one. `x ^ 2` and `x * x`
are the same monomial; degree above two and a linear term inside the brackets are both
refused by name. Division is exact and reduced (`mkReal` takes rational text, so `/ 3` is
`1/3` rather than a rounded decimal).

This is where LP differs from MPS, whose sections carry the `1/2` as part of the format and
never write it (`mps.md` §4.7) — and that difference is what makes the pair a good oracle.
HiGHS ships `qjh` as both `qjh.lp` and `qjh.mps`: one model, two formats, two frontends, two
unrelated ways of stating the quadratic part. `test_lp_quadratic.cpp` requires them to emit
the same objective, which no consistent misreading of either can satisfy.

The consequence is not a fidelity loss but a **logic change**: QF_LRA becomes QF_NRA, which
is a different decision problem with different solver support. That belongs in the report
as a feature count, which is exactly what step 4 of `translate()` records
(`src/translation/translate.cpp:616-618`), and the profile's `min_fidelity` floor is not the right
place to catch it.

Note also the `/ 2` in the quadratic syntax: LP's quadratic sections conventionally write
the form divided by two, which is a *notation*, not a division to translate. Getting it
wrong scales every quadratic coefficient by 2.

### 4.6 Dialect divergences that are semantic, not cosmetic

| Question | Divergence | Consequence if guessed |
|---|---|---|
| Is `1e30` a number or infinity? | some readers treat large magnitudes as ±∞ | a bound that should be absent becomes a real, very loose bound — or an intended `1e30` becomes infinity |
| Are variable names case-sensitive? | dialects differ | two variables silently become one |
| What characters may a name contain? | dialects differ | parse failure, or worse, a truncated name colliding with another |
| Is an empty objective legal? | mostly yes | — |
| May a variable appear twice in one row (`x + x`)? | usually summed | dropping one halves the coefficient |

The first row is the dangerous one because it is a *magic constant*: the file says `1e30`
and the meaning depends on the reader. Pin the dialect (§1), implement its rule, and record
the dialect in `Provenance::language_version` so a result row says which reading produced
it.

---

## 4.6 What building it settled

**§4.1 is moot, and the obligation it generated with it.** That section proposed scaling rows
by the least common multiple of their denominators, because the HIR had no real literal, and
required the scale factor to be recorded or "the reported optimum is wrong by a factor nobody
wrote down". `ExprKind::LIT_REAL` landed on 2026-08-12 and keeps a decimal exactly — `0.1`
comes out as `(/ 1 10)`, which *is* one tenth — so nothing is scaled and there is no factor.
The scaling obligation is retired rather than satisfied.

**The remaining four obligations are all one shape**, and the frontend is small enough that it
is easy to see: each is a line of code whose absence produces a *strictly more permissive*
model. Non-negativity dropped, Binary's bounds overridden by a `Bounds` entry, a
semi-continuous variable read as `[0, u]`, `<` read as strict — the first three admit points
the file excludes, and the fourth excludes points the file admits. Only the last one fails
loudly, and only sometimes.

The semi-continuous case is the sharpest: the interval reading admits every value between 0
and *l*, which is precisely the band the modeller wrote the section to exclude, so the
"optimum" it reports can lie inside it.

**Indicator constraints and SOS are refused rather than
approximated**, and all three appear in `coverage().missing`.
`E_UNSUPPORTED_CONSTRUCT` is the right bucket: these are valid LP features and the gaps
belong to this frontend.

**Exact mathematics and numerical solver acceptance are different layers.** LP decimal
tokens denote rational coefficients in this adapter. HiGHS' `2122.lp` is exactly infeasible:
an unsat core forces `x623 = -2000/102294058333333` together with `x623 >= 0`.
CPLEX 22.1 accepts the approximately `-1.96e-11` violation under its feasibility tolerance.
That operational tolerance must not be silently imported into the source satisfaction
relation; comparisons against floating LP solvers must report it as a solver-policy
difference.

---

## 5. New HIR surface this format forces

| Surface | Needed for | Also needed by |
|---|---|---|
| ~~**`ExprKind::LIT_REAL`, holding a rational**~~ **landed 2026-08-12**, accepting both `1.5` and `1/3` | every non-integer coefficient (§4.1) | MPS, MiniZinc (`float`), FlatZinc |
| ~~**`ExprKind::LIT_BIGINT`**~~ **landed 2026-08-12** as text-backed `LIT_INT`; `LIT_REAL` already carried exact rationals | the scaled-integer rescue, and integer coefficients beyond `long long` (§4.1) | OPB/WBO |
| `Op::ITE` | semi-continuous variables, SOS counting (§4.4) | FlatZinc, XCSP3, MiniZinc |
| `Op::IMPLIES` | indicator constraints (§4.4) | MiniZinc, XCSP3 |

**Not needed**: arrays, sets, quantifiers, comprehensions, transition systems, or any
cluster A/C/D surface. LP genuinely is a small language — its cost of 0.5× in
`docs/languages-scoping.md` §3.2 is about right *as a grammar estimate*; what that estimate
missed is that the two literal kinds above are prerequisites, not conveniences.

`Op::DIV_REAL` is listed as proposed for completeness — LP's quadratic `/2` notation does
not need it (§4.5), and division by a constant can be folded into the coefficient, so it is
the lowest-priority item here.

---

## 6. Fidelity summary

**Exact on accepted paths.** Linear variables and bounds, comparison spellings, ranges,
integrality and binary carriers, semi-continuous/semi-integer variables, exact constants,
and one objective in either direction preserve models and objective values.

**Inherently lossy: nothing.** LP is a linear (or quadratic) arithmetic problem and SMT's
LRA/LIRA/NRA theories express it exactly. No construct in the format needs an
approximation.

**Blocked, not lossy:** quadratic expressions, indicators, and SOS currently return
`E_UNSUPPORTED_CONSTRUCT`; no approximate target model is emitted.

**Ways to make it lossy by mistake**:

- Omitting the implicit `x ≥ 0` (§4.2). **Unsound, silent, and the most likely first bug.**
- Reading `<` as strict (§2.4). Changes the model; in a continuous LP it can turn a feasible
  problem infeasible at the boundary.
- Scaling coefficients to integers without recording the objective's scale factor (§4.1).
  Reports a wrong optimum.
- Representing a decimal as a `double` (§4.1). Silently misreads the file; no `Fidelity`
  value describes it because it is not an approximation of the model.
- Guessing a dialect's `1e30`-is-infinity rule (§4.6).
- Halving or doubling quadratic coefficients by mishandling the `/2` notation (§4.5).

---

## 7. References

**Format documentation**

1. [IBM CPLEX LP file format reference](https://www.ibm.com/docs/en/icos/22.1.0?topic=cplex-lp-file-format), version 22.1.
2. Gurobi LP format reference. **Not re-confirmed.**
3. GLPK reference manual, CPLEX-LP reader. **Not re-confirmed.**

There is no vendor-independent standard; see §1.

**Corpus**

4. MIPLIB 2017 — the ranked corpus for this problem class, distributed in MPS. See
   `mps.md` §1.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster B — **corrected by §4.1 of this document**),
   §3.2 (0.5×), §4 (Plan 2).
6. `docs/languages/dimacs-cnf.md` §5 (the only cluster-B member needing no footnote),
   §2.2 (the vacuous-`preserves_optimum` reading §4.3 contrasts with).
7. `docs/languages/opb-wbo.md` §4 (`ExprKind::LIT_BIGINT`, which §4.1's rescue runs into).
8. `docs/languages/mps.md` §2.4 (`RANGES`), §4.2 (the second bound trap).
9. `docs/known-defects-2026-08-11.md` §4 (why the §4.2 fixture must be one that fails
   without the fix).
10. `include/somtparser/hir/hir.h`, `include/somtparser/frontend/parser.h`,
    `src/hir/hir.cpp`, `src/translation/translate.cpp`, `src/lowering/omt_emitter.cpp`.


### Reader boundaries verified on 2026-09-23

The inline constraint-header form in upstream `1449b.lp` is accepted by Gurobi
13.0.3: it means minimize `a`, with `a >= 1`, optimum 1. Its rejection by HiGHS
1.15.1 is a reader-conformance difference, not evidence that it lacks a defined
interpretation. The frontend now recognizes `subject to`, `such that`, `st`, and
`s.t.` after objective tokens on the same physical line and records
`gurobi-inline-constraint-header`. This does not allow arbitrary same-line section
switches: upstream `1449a.lp`, with inline `bounds`, remains refused as it is by
Gurobi. See the [upstream reader test](https://github.com/ERGO-Code/HiGHS/blob/73cac48c5340d775a477087198611862559be250/check/TestFilereader.cpp)
and the independently recorded reference imports.

A separate silent-error fix preserves labels named after section keywords.
Previously `end: x - 1 >= 2` ended parsing and discarded both this constraint and
the following integrality section. The unchanged upstream `1451.lp` now retains
both. With `lhs_numbers=constants` (the existing mathematical extension) its
minimum is 3; `lhs_numbers=variables` selects Gurobi's actual interpretation,
which introduces a nonnegative variable named `1` and has minimum 2. Both
interpretations are recorded as encoding choices whenever a standalone LHS
numeral occurs. HiGHS also returns 2 here but drops the numeral from the row,
so identical optima alone do not establish the same source model.
This file already counted as a successful conversion;
its correction therefore improves semantics without raising the coverage count.
`test/python/test_lp_mps_reader_boundaries.py` checks feasible sets and optima,
including keyword labels and partial keyword words used as variable names.

### Explicit inline-bounds extension

`--opt inline_bounds=true` additionally recognizes `bounds` or `bound` after a
complete constraint as a section boundary on the same physical line. The
frontend already permits EOF without `End`; this option makes the additional
layout convention explicit. It records `explicit-inline-bounds` in the
translation report. The default reader still rejects upstream `1449a.lp`.

With this option, that **unchanged** source becomes minimize `a` subject to
`a >= 1` and `a <= 0`, and the resulting SMT is UNSAT. This is a defined reader
extension, not a claim that Gurobi or strict CPLEX accepts the source. The
[upstream discussion](https://github.com/ERGO-Code/HiGHS/issues/1449#issuecomment-1755940456)
and an independent HiGHS run on the explicitly labeled `End`-terminated variant
support this interpretation. The appended-`End` comparison file is not counted
as a corpus conversion. The actual conversion uses the original source bytes.

Tests also compare the complete feasible set and objective for a feasible
neighbour (`1 <= a <= 3`, minimum 1), keep labels and LHS variables named
`bounds`, handle preceding rows and continuation lines, and reject incomplete
rows. Thus passing the original UNSAT instance alone cannot hide an exporter
that simply outputs false. `scripts/audit-lp-inline-bounds.py` checks both CLI
and Python and writes the original hash, emitted SMT and selected-reader report.
