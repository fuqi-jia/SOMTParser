# MPS — the mathematical programming interchange format

**Updated**: 2026-09-23
**Status**: linear models and quadratic objectives implemented
(`languages/mps/`, `test/languages/test_mps.cpp`). SOS, quadratic constraints,
and indicators are refused explicitly.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster **B**, §3.2 (cost **0.7×**), §4.

## Explicit HiGHS warning recovery

The default reader remains strict. `highs_warning_recovery=1` selects the finite
numeric warning-recovery interpretation used by the HiGHS regression corpus:
undefined rows in COLUMNS/RHS/RANGES are ignored; the first nonzero linear
matrix/cost entry and first RHS/range/simple bound value are retained; RANGES
on free rows are ignored; bounds can introduce a column; and a negative UP
retains the default zero lower bound. Each recovered record is diagnosed and
copied into the translation report. Conflicting duplicate bounds that write
both endpoints remain refused. This option does not emulate floating-point
tolerances, accept NaN, or turn arbitrary text into an empty model.

The reference receipt
records HiGHS 1.15.1's import matrices and statuses. Its
[upstream test](https://github.com/ERGO-Code/HiGHS/blob/73cac48c5340d775a477087198611862559be250/check/TestFilereader.cpp)
expects `warnings.mps` to return a warning. The imported model has ten columns,
six rows, first-entry costs of -1 for C0 through C8, and inconsistent bounds;
the resulting UNSAT is a mathematical property of that selected interpretation.
Calling the file universally malformed was too strong: strict rejection and
explicit warning recovery are different reader contracts.

Reference acceptance alone is insufficient. In the same audit, `1448.lp` and
`garbage.lp` became empty models, `nan0.mps` retained a NaN objective, and
`nan1.mps` lost a NaN matrix entry. Those behaviors are not adopted.


<!-- rejected-hir: ExprKind::LIT_BIGINT -->
<!-- Considered and deliberately not built; see docs/languages/opb-wbo.md §4.6.
     The gap it names is closed by a text-backed LIT_INT instead. -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

**Headline result of the audit in §4**: MPS shares LP's literal gap exactly — cluster B's
"fits `ConstraintModel` today" is wrong for the same reason, and `lp.md` §4.1 is where that
correction is argued rather than repeated here. What MPS adds is **two sign conventions
that are traps rather than difficulties**, and both produce silently wrong models:

- **`RANGES`** (§4.1): the interval a range value denotes depends on the *row type*, and for
  an `E` row it depends on the *sign of the range value itself*. Get it wrong and the
  constraint is a different constraint, with no diagnostic.
- **`BOUNDS` type `UP` with a negative value** (§4.2): by long-standing convention many
  readers *also* set the lower bound to −∞, because a variable's implicit lower bound of 0
  would otherwise make the bound infeasible. Readers disagree. The same file means different
  things to different tools.

The second is worse than the first because it is a divergence between *implementations*, not
a subtlety of one specification — so "read the spec carefully" does not resolve it, and
whichever rule is chosen must be recorded in provenance.

MPS is also the **corpus-bearing half** of the LP/MPS pair: MIPLIB 2017 is distributed in
MPS, so this is where the measurement arm actually gets its instances (§1).


<!-- implicit-constraints:
  a column with no BOUNDS entry => VarDecl::lower_bound = 0, as LP (§2.5)
  columns between MARKER INTORG and INTEND => integer; ignoring the markers solves the LP relaxation and reports its optimum (§2.3, §4.3)
  BOUNDS BV => integer and [0,1], overriding anything else (§2.5)
  BOUNDS UP with a negative value => by common practice the lower bound also goes to -inf; readers disagree, so the chosen rule must be recorded in Provenance and warned per instance (§4.2)
  a RANGES entry on an E row => the row stops being an equality; which side the interval extends to depends on the sign of the range value (§2.4, §4.1)
  the second and later N rows => free rows constraining nothing, not constraints (§2.2)
-->
---

## 1. What the format is

MPS (Mathematical Programming System) is the column-oriented, section-based interchange
format for linear and mixed-integer programs. It dates to IBM mainframe practice and its
fixed-column layout still shows. Every LP/MIP solver reads it; it is what tools exchange,
where LP (`lp.md`) is what people write.

### Fixed and free format

| Variant | Layout | Consequence |
|---|---|---|
| **Fixed** MPS | fields at prescribed column positions (roughly 2–3, 5–12, 15–22, 25–36, 40–47, 50–61) | names may contain spaces; a name is delimited by *position*, not by whitespace |
| **Free** MPS | whitespace-separated | names may **not** contain spaces; simpler, and what modern tools emit |

A reader must decide which it is reading. Guessing wrong on a file with spaces in names
produces a silently mangled model — the field split lands in the wrong place and a name is
truncated or merged. The safest policy is to require free format and refuse fixed format
with `E_UNSUPPORTED_CONSTRUCT` unless a fixture proves the fixed reader works, since a
truncated name that happens to collide with another variable is a wrong answer with no
diagnostic.

### Standard documents

There is no vendor-independent standard, exactly as for LP (`lp.md` §1). The operative
references are the IBM/CPLEX MPS documentation, Gurobi's, and GLPK's, plus the MIPLIB
project's notes on what its files use. This implementation follows the IBM CPLEX 22.1
standard-record rules and identifies its accepted dialect as free-form MPS in
`Language::version()`.

### Corpus — and this is the one that matters

**MIPLIB 2017** is the curated, versioned benchmark library for mixed-integer programming,
distributed in MPS with per-instance metadata and a documented benchmark subset. It has the
three properties `docs/languages-scoping.md` §7's audit asks for: a corpus, reference
implementations (every MIP solver), and published results.

It also passes the second filter (§6 there): a MIP instance asks "is there a feasible
assignment, optimal for this objective", which is what an OMT solver answers. No
reinterpretation is needed, unlike SyGuS-IF (`sygus-if.md`) or SYNTCOMP (`syntcomp.md`).

**Instance counts, archive sizes and licence terms: not re-confirmed in this pass.** MIPLIB
instances carry per-instance licence/source notes, so republishing *translated* instances
needs the same check `docs/languages-scoping.md` §1.7 records for TPTP.

The realistic reading: **MPS is the LP/MPS pair's experiment arm, LP is its convenience
door.** `lp.md` §1 says the same from the other side.

---

## 2. Semantics — what a file means

### 2.1 Sections

```
NAME          EXAMPLE
ROWS
 N  COST
 L  LIM1
 G  LIM2
 E  MYEQN
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    XONE      COST         1.0        LIM1         1.0
    MARKER                 'MARKER'                 'INTEND'
    YTWO      COST         2.0        LIM1         1.0
    YTWO      MYEQN       -1.0
RHS
    RHS       LIM1         4.0        LIM2         10.0
RANGES
    RNG       LIM1         2.5
BOUNDS
 UP BND       XONE         4.0
ENDATA
```

| Section | Content |
|---|---|
| `NAME` | problem name |
| `OBJSENSE` | `MAX` or `MIN` (an extension; absent means minimise) |
| `ROWS` | one line per row: type `N`/`L`/`G`/`E` and a name |
| `COLUMNS` | non-zero coefficients, **column by column**, with `MARKER` lines toggling integrality |
| `RHS` | right-hand sides |
| `RANGES` | §2.4 |
| `BOUNDS` | §2.5 |
| `SOS` | special ordered sets (an extension) |
| `QUADOBJ` / `QMATRIX` | quadratic objective (an extension) |
| `INDICATORS` | indicator constraints (an extension) |
| `ENDATA` | end |

### 2.2 Rows, and which one is the objective

`N` rows are **free** rows: unconstrained. By convention the **first** `N` row is the
objective and any further `N` rows are ignored (or kept as free rows that constrain
nothing). That convention is not universal, and a file with several `N` rows is a place
where readers can differ — worth a warning rather than a silent choice.

`L` is `≤ rhs`, `G` is `≥ rhs`, `E` is `= rhs`. A row with no `RHS` entry has right-hand
side 0.

### 2.3 Columns and integrality markers

`COLUMNS` lists coefficients grouped by variable, two `(row, value)` pairs per line. A
variable that appears in no row still exists if it appears in `COLUMNS` or `BOUNDS`.

`MARKER` lines with `'INTORG'` / `'INTEND'` bracket the columns that are **integer**.
Everything outside such a bracket is continuous. The marker is positional state, so a
frontend that ignores marker lines silently makes every variable continuous — a *relaxation*
of the model: `complete = true`, `sound = false`, and the LP relaxation of a MIP is a
strictly easier and different problem.

Under CPLEX's MPS rule, a marker integer with no selected `BOUNDS` record defaults to
`0..1`; once it has a bound record it uses the ordinary integer defaults specified by that
record. This is not the same as merely changing the variable's sort to `Int`.

### 2.4 `RANGES` — the sign convention

A `RANGES` entry attaches a range value `R` to an already-declared row, turning a one-sided
constraint into a two-sided one. **What interval it denotes depends on the row type, and for
`E` rows on the sign of `R`:**

| Row type | Sign of `R` | Resulting interval |
|---|---|---|
| `L` (`≤ rhs`) | any | `[rhs − |R|, rhs]` |
| `G` (`≥ rhs`) | any | `[rhs, rhs + |R|]` |
| `E` (`= rhs`) | `R ≥ 0` | `[rhs, rhs + R]` |
| `E` (`= rhs`) | `R < 0` | `[rhs + R, rhs]` |

The `E` rows are the trap. An equality row with a range is no longer an equality, and which
side the interval extends to is decided by a sign the reader must inspect.

*Verified 2026-08-12* against the lp_solve MPS reference, which states the same four rows
explicitly (`G: [b, b+|r|]`, `L: [b-|r|, b]`, `E` with `r ≥ 0`: `[b, b+|r|]`, `E` with
`r < 0`: `[b-|r|, b]`).

### 2.5 `BOUNDS` — the types

As in LP (`lp.md` §2.2), a variable's **default domain is `[0, +∞)`**. `BOUNDS` overrides:

| Type | Meaning |
|---|---|
| `UP` | upper bound — **and see §4.2** |
| `LO` | lower bound |
| `FX` | fixed: lower = upper = value |
| `FR` | free: `(−∞, +∞)` |
| `MI` | lower bound `−∞` (upper stays `+∞` unless set) |
| `PL` | upper bound `+∞` (the default) |
| `BV` | binary: `{0, 1}`, and integer |
| `LI` / `UI` | integer lower / upper bound |
| `SC` | semi-continuous: `x = 0 ∨ l ≤ x ≤ u` (`lp.md` §4.4) |
| `SI` | semi-integer: the same disjunction over an integer carrier |

For `SC` without an explicit lower bound, CPLEX uses positive-band lower bound 1. This
differs from the LP section spelling and is kept in the MPS adapter rather than a shared
syntax rule.

### 2.6 What a solution is

Identical to LP (`lp.md` §2.6): an assignment satisfying every row and bound, optimal for
the objective row. MIPLIB additionally distributes reference solutions, which makes
model-level differential comparison possible and not just verdict-level — the
`dimacs-cnf.md` §3 distinction, on the good side for once.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| continuous column | `VarDecl{Sort::real()}` + implicit `≥ 0` (§2.5) | none for the decl | `exact()` |
| column inside `INTORG`/`INTEND` | `VarDecl{Sort::integer()}` + implicit `≥ 0` | none | `exact()` |
| **coefficient** | `ExprKind::LIT_REAL`, exact (landed 2026-08-12) | none | **`lp.md` §4.1** |
| `N` row (first) | `Objective{kind, term}` (`include/somtparser/hir/hir.h`) | none | `exact()` |
| `N` row (subsequent) | dropped, with a warning (§2.2) | none | `exact()` |
| `L` row | `Constraint{LE(Σ aᵢxᵢ, rhs)}` | none | `exact()` |
| `G` row | `Constraint{GE(…)}` | none | `exact()` |
| `E` row | `Constraint{EQ(…)}` | none | `exact()` |
| row with a `RANGES` entry | `AND(GE(…, lo), LE(…, hi))` per §2.4 | none | `exact()` **if the table is right** |
| `RHS` on the objective row | the negative of the objective constant | none | `exact()` |
| `BOUNDS UP/LO/FX/FR/MI/PL` | `VarDecl::lower_bound` / `upper_bound` | none | `exact()`, but §4.2 |
| `BOUNDS BV` | `integer()`, `[0,1]` | none | `exact()` |
| `BOUNDS SC` | disjunction (`lp.md` §4.4) | `Op::ITE` or a disjunction | `exact()` |
| `SOS` section | as `lp.md` §4.4 | `Op::ITE` | `exact()` |
| `QUADOBJ` / `QMATRIX` / `QSECTION` | `Op::MUL` terms; sets `feat::nonlinear()` (landed 2026-09-20, §4.7) | none | `exact()` (`lp.md` §4.5) |
| `INDICATORS` | implication | `Op::IMPLIES` | `exact()` |
| `OBJSENSE MAX` | `ObjKind::MAXIMIZE` | none | `exact()` |

For at least 65,536 non-`N` rows or 65,536 matrix entries in those rows,
the frontend stores the linear matrix in
immutable packed HIR batches with exact decimal coefficients, row relations,
bounds and source lines. Type checking validates this storage before SMT
assertions are streamed; declarations, domains and objectives use the ordinary
lowering path. These translations report `usesPackedSmtStream()` and expose
`writeSmt2()` / `toSmt2()`; `hasParser()` is false because there is no complete
materialized parser tree.

---

## 4. Semantic gaps and encoding choices

### 4.1 `RANGES` on an equality row

§2.4 states the convention. This section states the consequence.

Consider `MYEQN: x + y = 5` with `RANGES RNG MYEQN 2.0`. Under the table, the row becomes
`5 ≤ x + y ≤ 7`. Under the *opposite* sign reading it becomes `3 ≤ x + y ≤ 5`. Under the
"ignore `RANGES` for `E` rows" reading — which a frontend might arrive at by treating
`RANGES` as an `L`/`G` feature — it stays `x + y = 5`.

| Reading | Solution set vs. the intended one | Detected by |
|---|---|---|
| correct | equal | — |
| wrong sign | disjoint except at the boundary | nothing in the pipeline |
| range ignored on `E` rows | strictly smaller (over-constrained) | nothing |

All three parse. All three type-check. All three round-trip. Two of them answer a different
question, and one of those two is *over*-constrained, which means it can report UNSAT for a
feasible instance — the rarer and more embarrassing direction.

**The right defence is a fixture, not care.** An MPS file with an `E` row plus a positive
range and a second with a negative range, each with a known feasible point that is *outside*
the interval the wrong reading would produce. `docs/known-defects-2026-08-11.md` §4's lesson
applies directly: a fixture that passes under the wrong reading is not a test of this.

### 4.2 `BOUNDS UP` with a negative value — an implementation divergence

A variable's default lower bound is 0 (§2.5). Now consider:

```
 UP BND       X            -3.0
```

Read literally this is `0 ≤ X ≤ −3`, which is infeasible. Because a file that says this
almost certainly means something else, **many readers additionally set the lower bound to
−∞**, yielding `−∞ ≤ X ≤ −3`. Others set it to the bound value. Others take it literally
and let the model be infeasible.

*Verified 2026-08-12*, and the divergence is real and documented: CPLEX resets the lower
bound to −∞ **only when the upper bound is strictly less than 0**, and deliberately deviates
from other readers at exactly `UP 0` — where it keeps the lower bound at 0, fixing the
variable, rather than opening it to −∞. So the boundary case `UP 0` is a *third* behaviour,
distinct from both readings above, and a frontend must decide it separately from the
negative case.

This is not a subtlety within one specification. It is a **disagreement between
implementations**, so no amount of careful reading resolves it — and it means an MPS file
with a negative `UP` bound does not have a single meaning.

| Policy | Consequence |
|---|---|
| Literal (`[0, −3]`, infeasible) | matches the text; disagrees with most tools; will report UNSAT where solvers report SAT |
| Lower bound to −∞ | matches common practice; changes the model relative to the text |
| Refuse with `E_UNSUPPORTED_CONSTRUCT`, naming the ambiguity | loses instances but never answers a question the file did not ask |

**Recommendation**: implement the common-practice reading, because the corpus was produced
by tools that use it, and **record it** — both in `Provenance` and as a `WARNING` diagnostic
on any instance where it fired, so an experiment can count how many results depend on the
choice. A silent choice here is a result nobody can reproduce from the file alone.

This is the clearest case in the batch for a diagnostic that is neither an error nor
silence, and `Uir::Diagnostics` already has the severity for it
(`Severity::WARNING`, `include/somtparser/translation/diagnostic.h:42`).

### 4.3 The integrality marker is positional state

§2.3 states it; the failure mode is worth its own line because it is easy to get *partly*
right. A frontend that handles `INTORG`/`INTEND` but resets the state at a section boundary,
or that treats the markers as applying to rows rather than columns, produces a model where
*some* variables are wrongly continuous. That is an LP relaxation of part of the MIP —
weaker than the original, `sound = false`, and it will still find optima, just wrong ones.

The test is again a fixture: a small MIP whose LP relaxation has a strictly better optimum
than its integer optimum. If the frontend loses integrality, the reported optimum improves,
which is a *visible* symptom — unlike most of the traps in this document.

### 4.4 Everything LP has

The rest of MPS's semantic surface is LP's, and `lp.md` carries it:

| Topic | Where |
|---|---|
| the missing real literal, and the scaled-integer rescue that overflows `long long` | `lp.md` §4.1 |
| the implicit `x ≥ 0` and what dropping it costs | `lp.md` §4.2 |
| maximisation and `preserves_optimum` | `lp.md` §4.3 |
| semi-continuous variables, SOS sets, indicator constraints as disjunctions | `lp.md` §4.4 |
| quadratic sections and the move from LRA to NRA | `lp.md` §4.5 |
| infinity conventions and other dialect divergences | `lp.md` §4.6 |

Two additions specific to MPS:

- **The objective row's `RHS`.** Some dialects treat an `RHS` entry on the objective row as
  the *negated* constant term. Confirm the sign for the chosen dialect; a sign error here
  shifts every reported optimum by a constant, which is the least visible kind of wrong
  answer because the argmin is unaffected.
- **A companion basis or solution file.** `SourceUnit::data_paths` exists for this
  (`docs/languages-scoping.md` §3.2 notes it), and `Language::acceptsDataFiles()` must be
  overridden if such a file is ever accepted (`include/somtparser/translation/language.h:105`) —
  otherwise `translate()` refuses the pair, which is the correct default
  (`src/translation/translate.cpp:376-388`).

### 4.5 Fixed-format parsing

Not a semantic gap but the largest source of *lexical* wrongness, and the reason
`docs/languages-scoping.md` §3.2 prices MPS at 0.7× against LP's 0.5× despite identical
semantics. §1 recommends requiring free format until a fixed-format reader is proven by
fixtures, on the grounds that a mis-split field is a wrong model with no diagnostic.

---

## 4.6 What building it settled

**Three of the six obligations are markers rather than data** — state a reader carries
between lines and that no single line shows. That is what makes them invisible to review as
well as to a parser: `MARKER 'INTORG'`, the first-`N`-row convention, and a `RANGES` entry
that changes what an `E` row means. A reviewer reading a COLUMNS line cannot tell whether the
column is integer, and neither can a frontend that does not carry the bracket.

The `RANGES`-on-`E` sign rule is the sharpest, and the test is the two-fixture pair: the same
row with `+3` and `−3` gives `[10, 13]` and `[7, 10]`. Taking `|R|` yields the first for both
— wrong on half the instances, and wrong in *neither* direction consistently, so it is not an
approximation with a `Fidelity` but a different problem.

**§4.2's divergence is warned per instance rather than resolved.** The rule taken is CPLEX's:
open the lower bound to −∞ only when the upper is *strictly* below zero. `UP 0` therefore
keeps the lower bound at 0 and fixes the variable, which is the third behaviour §4.2 records
and the one a rule phrased as "negative upper bound opens the lower one" gets wrong. Both
cases are fixtures.

**Scientific notation is legal MPS and is not an SMT-LIB numeral.** `1.5e2` and `1e-3` are
expanded to plain decimals *as text*, because routing them through a `double` is exactly what
`ExprKind::LIT_REAL` exists to avoid — and `1e-3` is a thousandth exactly, which a double is
not.

`RANGES` arithmetic is exact for the same reason: `rhs ± |R|` is computed on decimal strings,
so `4.0 − 2.5` comes out `1.5` and lowers to `(/ 3 2)`.

---

### 4.7 The quadratic sections carry a `1/2`, and three spellings of one matrix

The objective is `c'x + ½ x'Qx`, and the `½` is carried by the FORMAT as a notation rather
than written as a division. Three sections state `Q`:

| entry | contributes to the coefficient of |
|---|---|
| `Xi Xi v` — diagonal, any section | `(v/2)·xi²` |
| `Xi Xj v` — off-diagonal, `QUADOBJ` / `QSECTION` | `v·xi·xj` |
| `Xi Xj v` — off-diagonal, `QMATRIX` | `(v/2)·xi·xj` |

`QUADOBJ` and `QSECTION` give one triangle, so an off-diagonal entry stands for its mirror
as well and the two halves add back to `v`; `QMATRIX` gives both triangles and each entry is
halved. Repeated entries **sum** rather than overwrite, and the key is the *unordered* pair,
so `X1 X2` and `X2 X1` are one monomial.

Getting any of those three rules wrong produces a model that still type-checks and still
solves, and answers a different question — `lp.md` §4.5 names the failure for the `½` alone.
They are settled by HiGHS's own regression set rather than by reading: `2821.mps`,
`2821-duplicate.mps` (a repeated entry), `2821-summation.mps` (both triangles in a `QUADOBJ`)
and `2821-qmatrix.mps` state **one model four ways**, and `test_mps_quadratic.cpp` requires
all four to emit byte-identical output. Each wrong rule breaks a different member.

Halving is exact decimal arithmetic, not a `double`: `0.2` becomes the rational `1/10`.

`QSECTION` names its row in the header. Only the objective row is implemented — a quadratic
*constraint* is a different construct, refused by name rather than added to the objective,
which would move its terms from a bound the model states to a quantity it minimises. A file
carrying **both** a `QUADOBJ` and a `QMATRIX` (HiGHS ships `qjh_quadobj_qmatrix.mps`) is also
refused: reading both would double every coefficient and picking one would be a silent choice
between two statements of the model.

## 5. New HIR surface this format forces

Identical to LP's, which is the point:

| Surface | Needed for | Also needed by |
|---|---|---|
| ~~**`ExprKind::LIT_REAL`**, holding a rational~~ **landed 2026-08-12** | every non-integer coefficient, RHS, range and bound | LP, MiniZinc, FlatZinc |
| ~~**`ExprKind::LIT_BIGINT`**~~ **landed 2026-08-12** as text-backed `LIT_INT` | the scaled-integer rescue (`lp.md` §4.1) | OPB/WBO, LP |
| `Op::ITE` | semi-continuous variables, SOS sets | LP, FlatZinc, XCSP3, MiniZinc |
| `Op::IMPLIES` | `INDICATORS` | LP, MiniZinc, XCSP3 |

**Not needed**: arrays, sets, quantifiers, comprehensions, transition systems. MPS shares
LP's position in `docs/languages-scoping.md` §3.1 cluster B and shares the correction
`lp.md` §4.1 makes to it.

---

## 6. Fidelity summary

**Exact on accepted paths.** Rows of all four types, selected RHS/RANGES/BOUNDS vectors,
objective offsets, integrality markers and their defaults, SC/SI, and the objective in both
senses preserve models and objective values.

**Inherently lossy: nothing.** As LP: linear and quadratic arithmetic over integers and
reals is exactly what SMT's LIRA/NRA theories express.

**Blocked, not lossy:** SOS, quadratic *constraints*, and `INDICATORS` return
`E_UNSUPPORTED_CONSTRUCT`; no approximate target is emitted.

**Ways to make it lossy by mistake** — MPS has more of these than any other cluster-B
format, which is the real reason it costs more than LP:

- Misreading a `RANGES` entry on an `E` row (§4.1). **Silent; can over-constrain, hence
  UNSAT on a feasible instance.**
- Choosing a `BOUNDS UP`-with-negative-value rule without recording it (§4.2). **The file
  does not have one meaning; a silent choice is unreproducible.**
- Losing integrality by mishandling `MARKER` state (§4.3). **Solves the LP relaxation and
  reports its optimum.**
- Splitting fixed-format fields by whitespace (§1, §4.5). **Mangles names.**
- Taking the second `N` row as a constraint rather than a free row (§2.2).
- Getting the objective-row `RHS` sign wrong (§4.4). **Shifts every optimum by a constant;
  the argmin is unaffected, so it is nearly invisible.**
- And all of `lp.md` §6's list, which applies unchanged.

---

## 7. References

**Format documentation**

1. [IBM CPLEX MPS standard records](https://www.ibm.com/docs/en/cofz/22.1.2?topic=standard-records-in-mps-format), version 22.1.
2. Gurobi MPS format reference. **Not re-confirmed.**
3. GLPK reference manual, MPS reader. **Not re-confirmed.**

There is no vendor-independent standard; see §1 and `lp.md` §1.

**Corpus**

4. MIPLIB 2017 — the curated MIP benchmark library, distributed in MPS, with a documented
   benchmark subset and reference solutions. Instance counts and per-instance licence terms
   **not re-confirmed**; see `docs/languages-scoping.md` §1.7 for the republication question
   this shares with TPTP.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster B — corrected in `lp.md` §4.1), §3.2 (0.7×,
   and the `data_paths` note §4.4 refers to), §4 (Plan 2), §6 (the second filter),
   §7 (the competition audit).
6. `docs/languages/lp.md` — §4.1 through §4.6, which this document deliberately does not
   duplicate.
7. `docs/languages/dimacs-cnf.md` §3 (verdict-level versus model-level comparison, §2.6).
8. `docs/known-defects-2026-08-11.md` §4 (why §4.1's and §4.3's fixtures must fail without
   the fix).
9. `include/somtparser/hir/hir.h`, `include/somtparser/translation/diagnostic.h`,
   `include/somtparser/translation/language.h`, `src/translation/translate.cpp`.


### Trailing comments and marked names (2026-09-23)

The unchanged HiGHS `comment.mps` is accepted by Gurobi 13.0.3 and optimizes to
-4. The tokenized frontend now recognizes a trailing asterisk comment after a
complete row, coefficient, RHS/range, bound, or quadratic record. It records
`trailing-asterisk-comment`; it does not interpret arbitrary asterisks inside
names as comment starts. The existing dollar-comment handling had silently
truncated column names such as `$X`; it now uses the same record boundaries.
Declared rows beginning with `*` or `$` retain their coefficients. Ambiguous
undeclared marked rows followed by a numeric coefficient remain errors.

The fixed-field upstream file, its objective, all constraints and bounds were
checked against Gurobi. Free/fixed auto-detection is reader-specific: some
malformed free-field comment layouts are reinterpreted by Gurobi as fixed-field
names, and that recovery is not adopted. This frontend's explicit tokenized
record convention is stated here rather than claimed to emulate every reader.
