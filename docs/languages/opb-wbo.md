# OPB / WBO — pseudo-Boolean satisfaction, optimisation and weighted-Boolean optimisation

**Date**: 2026-08-11
**Status**: **implemented** (`languages/opb/`, `test/languages/test_opb.cpp`, and
`test/languages/test_pb_cross_format.cpp` for the half that only exists between two formats).
Written document-first: every obligation in the block below predates the code.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster B ("fits `ConstraintModel`
today, no new HIR feature"), §3.2 (cost 0.4×), §4 (Plan 2). §4 of this document reports
where that cluster-B classification survives contact with the actual header and where it
does not; §5 states the surface it forces.


The current finite-threshold implementation uses exact violation indicators:
`r_i = 0` if and only if the source row holds, with `r_i` in `{0,1}`. Thus the
emitted objective preserves every feasible assignment's cost, including
nonoptimal assignments. The earlier one-sided relaxation described in the
historical design comparison below preserved an optimum but allowed spurious
positive costs for satisfied rows. The independent source-relation checks in
`test/python/test_wbo_exact_cost_relation.py` cover this distinction, strict
thresholds, all comparison operators, nonlinear terms and arbitrary integers.


<!-- The names above are HIR this format would force, not HIR that exists.
     scripts/check-doc-citations.py keeps the two apart: it fails if one of
     them is a typo, and it fails again once one of them actually lands, so
     this document cannot go on calling it future work. -->


<!-- implicit-constraints:
  every variable => Boolean, i.e. VarDecl bounds [0,1] on an Int, because OPB uses x arithmetically in linear sums while its domain is {0,1} and no line declares it (§2)
  a negated literal ~x in a sum => the term (1 - x), not a separate variable (§2)
  WBO: a soft constraint's cost is incurred exactly when the constraint is violated => the objective term is the reification of its negation, which the file never writes (§2)
-->

<!-- rejected-hir: ExprKind::LIT_BIGINT -->
<!-- Considered and deliberately not built; see §4.6. -->

---

## 1. What the format is

OPB is the input language of the **Pseudo-Boolean Competitions** run at CRIL,
Université d'Artois. One grammar carries four problems, distinguished only by the first
non-comment line:

| Problem | First non-comment line | Question |
|---|---|---|
| PBS — pseudo-Boolean satisfaction | (none; a constraint) | is there a model? |
| PBO — pseudo-Boolean optimisation | `min: …;` (`max:` since 2024) | minimise a linear pseudo-Boolean objective |
| WBO — weighted-Boolean optimisation | `soft: T;` | minimise the total cost of violated soft constraints, subject to `cost < T` |
| model counting / enumeration | `models: count;` / `models: enumerate;` | count or list models (2024 extension) |

`.opb` carries PBS and PBO; `.wbo` carries WBO.

### Standard documents

The format was split into two documents for the 2024 competition. **The general document
is canonical for this project**; the restricted one describes what competition instances
actually contain, and is therefore what the corpus looks like.

| Document | Version | Date | URL |
|---|---|---|---|
| *General OPB Format*, O. Roussel | `$Rev: 4524$` | 2024-03-11 | <https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf> |
| *Restricted OPB Format in Use in the PB Competitions*, O. Roussel | `$Rev: 4524$` | 2024-03-11 | <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf> |
| *Input/Output Format and Solver Requirements for the Competitions of Pseudo-Boolean Solvers*, O. Roussel & V. Manquinho (the pre-2024 single document, cited as `[RM16]` by both of the above) | `$Rev: 2324$` | 2016-01-14 | <https://www.cril.univ-artois.fr/PB16/format.pdf> |

The 2024 general document lists its own changes against PB16: separation of general from
restricted format, `max:` as well as `min:`, all the usual relational operators
(including `!=`/`≠`), arbitrary identifiers for variable names, UTF-8, and the
model-counting extension. The restricted document adds two header hints, `#equal=` and
`intsize=`.

Both documents trace the format to the README of **OPBDP**
(<http://opbdp.sourceforge.net/>), extended across competitions PB05 → PB16 → PB24.

### Reference implementations and corpus

- **Competition site**: <https://www.cril.univ-artois.fr/PB24/> — Pseudo-Boolean
  Competition 2024, the most recent edition confirmed live. Tracks: PBS and PBO (each
  with and without certificates), a WBO track opened conditionally, and a potential
  non-linear track.
- **Corpus**: normalised instance archives per edition under
  `https://www.cril.univ-artois.fr/PB24/benchs/` and
  `https://www.cril.univ-artois.fr/benchs/`. Confirmed artefacts:
  `selected-PB24.tar` (255 MiB), `SampleByIntSize.tar` (128 MiB) — a sample deliberately
  stratified by coefficient magnitude, which is directly useful for §4's `long long`
  question — and `normalized-PB24.tar` (2.5 GiB). PB16's archives are `PB16.tar` and
  `PB16-used.tar` (>4 GB).
  **Instance counts: not found** as a published total on either edition's index page.
- **Licence**: **not found** as a formal licence. The competition states only that it
  "cannot accept benchmarks which are not publicly available (because anyone must be able
  to reproduce the experiments of the competition)". Treat redistribution of translated
  instances as unresolved, exactly as `docs/languages-scoping.md` §1.6 does for SyGuS-IF.
- **Reference solvers**: RoundingSat, Sat4j's PB frontend, NaPS and Exact are the
  commonly-cited PB solvers; **current versions and the PB24 winners were not confirmed
  in this pass** — pin one and verify it builds before differential testing starts, per
  the same rule `docs/languages-scoping.md` §1.2 applies to QDIMACS.

---

## 2. Semantics — what a file means

### 2.1 Vocabulary and models

Variables are **Boolean**, taking values in `{0, 1}`. A *literal* is a variable or its
negation `~x`. In the general format a variable name is an ASCII identifier
(`letter-or-underscore` then letters/digits/underscores) or a double-quoted string; in the
restricted competition format it is always `x` followed by a positive integer `< 2^32`,
and names are guaranteed to run contiguously `x1 … xN`, every one of them occurring in at
least one constraint or the objective.

A *term* is a coefficient followed by one or more literals. A *product* of literals
evaluates to 1 iff every literal in it is 1 — that is, a conjunction. Linear instances
restrict terms to a single literal.

A **model** is an assignment of `{0,1}` to every variable satisfying every constraint. For
PBS that is the answer. For PBO the answer is a model minimising (or, since 2024,
maximising) the objective. For WBO see §2.4.

### 2.2 Constraints

Grammar, quoted from *General OPB Format* §3.1:

```
<constraint>::= <sum> <relational_operator> <zeroOrMoreSpace> <integer> <zeroOrMoreSpace> ";"
<sum>::= <weightedterm> | <weightedterm> <sum>
<weightedterm>::= <integer> <oneOrMoreSpace> <term> <oneOrMoreSpace>
<relational_operator>::= "=" | "!=" | "≠" | ">" | ">=" | "≥" | "<" | "<=" | "≤"
```

So a constraint is `Σ_i a_i · t_i ⋈ d ;` where each `a_i` is a signed integer, each `t_i`
a term, `d` a signed integer *degree*, and `⋈` a relational operator. Every non-comment
line ends with `;`; a constraint occupies one line (which "may be very long" — the
document explicitly warns against reading a line as a whole).

**The restricted competition format permits only `>=` and `=`.** Everything else is
normalised away before an instance is published. A frontend that targets the corpus needs
only those two; a frontend that claims to read the general format needs all eight
spellings including the Unicode ones, and `!=` — which is a *disequality*, not a linear
constraint, and is the one operator with no direct linear counterpart.

Comments are lines beginning with `*`, allowed anywhere.

### 2.3 Numeric semantics — integers, and they are unbounded

This is the format's defining numeric decision and §2 of both format documents is devoted
to it:

> A pseudo-Boolean formula may use integers of arbitrary size, because this can simplify
> the encoding of different problems (such as the factorization problem).

There is **no floating point anywhere in OPB/WBO**: coefficients, degrees and soft costs
are all exact integers of unbounded width. The documents recommend GMP or Java
`BigInteger`, and the competition deliberately does not hide the problem — it classifies
benchmarks by coefficient size and lets a solver register only for the categories it can
read. The 2024 restricted format adds an `intsize=` header hint giving the number of bits
needed for the worst constraint, precisely so a fixed-width solver can decline an instance
at parse time rather than overflow silently.

The spec's own example instance contains

```
12345678901234567890 x4 +4 x3 >= 10;
```

That coefficient is `1.23 × 10^19`, larger than `LLONG_MAX = 9223372036854775807`
(`9.22 × 10^18`). **The canonical example in the format document does not fit
`Hir::Expr::int_value` (`long long`, `include/somtparser/hir/hir.h`).** See §4.1.

### 2.4 WBO: soft constraints and the top cost

A WBO file has no objective function. Its first non-comment line is `soft: T ;`, or
`soft: ;` for `T = ∞`. Hard constraints are written exactly as in a PBS file; a soft
constraint is prefixed by its cost in square brackets:

```
<softheader>::= "soft:" [<unsigned_integer>] ";"
<softconstraint>::= "[" <zeroOrMoreSpace> <unsigned_integer> <zeroOrMoreSpace> "]" <constraint>
```

Costs are strictly positive integers (big integers allowed), each strictly less than `T` —
a cost `≥ T` would make the constraint effectively hard.

The semantics, quoted from *General OPB Format* §3.2, are **not** simply "minimise
violated weight":

> The WBO problem consists in finding an assignment to the problem variables such that all
> hard constraints are satisfied and the total weight of the unsatisfied soft constraints
> is minimized **and strictly less than T**.

`T` is a hard admissibility threshold borrowed from WCSP, not a presentational hint. The
document's Example 3 is an instance whose minimum cost is exactly 6 with `soft: 6;` — and
the correct answer is `s UNSATISFIABLE`, not `s OPTIMUM FOUND` with cost 6. A translation
that drops `T` answers a different question on exactly this class of instance. See §4.4.

Competition instances soften this: *Restricted OPB Format* guarantees that when every
interpretation is admissible, `T` is published as `1 + Σ costs`, and the header carries
`#soft=`, `mincost=`, `maxcost=` and `sumcost=`. So a frontend can compare `T` against
`sumcost` and prove the threshold vacuous for most corpus instances.

### 2.5 Header hints

Not part of the grammar — they are comments — but guaranteed present in competition
instances and worth parsing, because two of them size the encodings in §4.

```
* #variable= 5 #constraint= 4 #equal= 1 intsize= 64
* #variable= 5 #constraint= 4 #product= 5 sizeproduct= 13
* #variable= 15 #constraint= 21 #soft= 5 mincost= 1 maxcost= 1 sumcost= 5
```

`#product=` is the number of distinct products and `sizeproduct=` the total number of
literals across those products; the document states outright that these exist so a parser
can pre-compute how many linear constraints a linearisation will produce. `intsize=` is
`max_i (1 + ⌊log₂(|d_i| + Σ_j |a_ij|)⌋)`. The presence of `#product=` is itself the
marker that the instance is non-linear.

### 2.6 Output

`s SATISFIABLE` / `s UNSATISFIABLE` / `s OPTIMUM FOUND` / `s UNKNOWN` / `s UNSUPPORTED`,
one `s` line, mandatory. `o <cost>` lines report improving objective values *in the
original file's units* — the document is explicit that a solver which internally rewrites
`-x` as `not(x) - 1` must undo the shift before printing. `v` lines list literals
(`v -x1 x2`). `s UNSUPPORTED` is the prescribed answer when a solver meets a feature it
cannot read, e.g. a non-linear constraint in a linear-only solver — a useful precedent for
what `E_UNSUPPORTED_CONSTRUCT` should map onto in differential testing.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

Two global decisions govern the whole table and are justified in §4.2:

- **Pseudo-Boolean variables become `SortKind::INT` with bounds `[0,1]`, not
  `SortKind::BOOL`**, whenever they occur inside a weighted sum.
- The objective is emitted through **one auxiliary variable plus one defining
  constraint**, because `omt_emitter.cpp:41` refuses any objective term that is not a bare
  identifier or an integer literal.

| Construct | HIR representation | New HIR surface required | Fidelity | Notes |
|---|---|---|---|---|
| `* comment` line | dropped | none | `exact()` | Header comments are parsed for hints (§2.5) but carry no semantics. |
| `#variable=` / `#constraint=` / `#equal=` | not represented; used for reserve/validation | none | `exact()` | Mismatch with the actual content is a diagnostic (`E_PARSE`), never a silent fix. |
| `intsize=` | not represented; used as a pre-parse guard | none | `exact()` | If `intsize > 63`, refuse with `E_UNSUPPORTED_CONSTRUCT` before building HIR — see §4.1. |
| Variable `xN` (in a weighted sum) | `VarDecl{name, Sort::integer(), lower=mkInt(0), upper=mkInt(1)}` | none | `exact()` | `hir_to_parser.cpp:144-155` emits both bounds as ordinary assertions. |
| Variable `xN` (purely propositional occurrence) | `VarDecl{name, Sort::boolean()}` | none | `exact()` | Only available when the variable occurs in no arithmetic sum anywhere in the file; in practice OPB always sums, so this case is rare. |
| Literal `x` | `mkIdent(x, INT)` | none | `exact()` | |
| Literal `~x` | `mkOp(SUB, {mkInt(1), mkIdent(x, INT)})` | none | `exact()` | `1 - x` is the format's own normalisation (§2.1 of the restricted document says linear files already have negations removed this way). |
| Weighted term `a x` | `mkOp(MUL, {mkInt(a), mkIdent(x, INT)})` | none | `exact()` | One non-constant factor, so `isNonlinearOperation` (`src/hir/hir.cpp`) does **not** flag `feat::nonlinear()`. |
| Sum `Σ a_i t_i` | `mkOp(ADD, {…})` | none | `exact()` | n-ary; `mkOp` accepts any arity ≥ 1. |
| `>= d` | `mkOp(GE, {sum, mkInt(d)})` | none | `exact()` | |
| `= d` | `mkOp(EQ, {sum, mkInt(d)})` | none | `exact()` | |
| `> d`, `<= d`, `< d` (general format) | `mkOp(GT/LE/LT, …)` | none | `exact()` | Present in `Hir::Op`; not needed for the competition corpus. |
| `!= d` / `≠ d` (general format) | `mkOp(NOT, {mkOp(EQ, {sum, mkInt(d)})})` | none | `exact()` | The only operator with no linear counterpart; exact in SMT, requires a disjunction or big-M in a MIP target. A genuine advantage of the SMT target. |
| Non-linear term `a l₁ l₂ … l_k` | see §4.3 — three candidate encodings | none for two of them | `exact()` or `equisat()` | Default recommendation: product variable + linearising constraints, `equisat()`. |
| `min: <sum> ;` | `obj` `VarDecl` (INT) + hard `Constraint{EQ(obj, sum)}` + `Objective{MINIMIZE, mkIdent("obj")}` | none | `equisat()` | The auxiliary variable is forced by `omt_emitter.cpp:41`, not by the source language. §4.2. |
| `max: <sum> ;` (2024 general format only) | same with `ObjKind::MAXIMIZE` | none | `equisat()` | Not emitted by the competition corpus. |
| absent objective (PBS) | `objectives` left empty | none | `exact()` | A pure decision problem. |
| `soft: T ;` with finite `T` | hard `Constraint{LE(Σ c_i r_i, mkInt(T-1))}` over the relaxation variables of §4.4 | none | `exact()` given §4.4's relaxation | Dropping it is `overApprox()` — see §4.4. |
| `soft: ;` (`T = ∞`) | nothing | none | `exact()` | |
| hard constraint in a `.wbo` file | `Constraint{formula, soft=false}` | none | `exact()` | |
| `[c] <constraint>` soft constraint | `Constraint{formula, soft=true, weight=c}` **or** the relaxation encoding of §4.4 | none in the struct; **a lowering does not exist** | `exact()` / `equisat()` | `hir_to_parser.cpp:163-172` currently *refuses* any `soft` constraint. See §4.5. |
| `#soft=`, `mincost=`, `maxcost=`, `sumcost=` | not represented; used to prove `T` vacuous and to check `int64` fit | none | `exact()` | |
| `models: count ;` / `models: enumerate ;` / `project:` (2024) | not represented | out of scope | — | Model counting is not a satisfiability question; `docs/languages-scoping.md` §6.3 declines the Model Counting Competition on exactly this ground. Refuse with `E_UNSUPPORTED_CONSTRUCT`. |

---

## 4. Semantic gaps and encoding choices

### 4.1 Arbitrary-precision integers versus `long long int_value`

**The gap.** `Hir::Expr` carries `long long int_value` (`include/somtparser/hir/hir.h`)
and `mkInt(long long)` (`src/hir/hir.cpp`) is the only numeric constructor. OPB
coefficients, degrees and soft costs are unbounded integers by explicit design (§2.3), and
the format document's own example exceeds `LLONG_MAX`. This is a real gap, not a
theoretical one: the competition publishes a `SampleByIntSize.tar` archive stratified by
coefficient magnitude, and classifies solvers by which sizes they can read.

Note that the *target* has no such limit — `Parser::mkConstInt(const Integer&)`
(`include/somtparser/frontend/parser.h:1109`) and the GMP-backed `Integer`/`Rational` in
`include/somtparser/ir/number.h` handle arbitrary precision. The ceiling is imposed by the
HIR layer alone, which is the same shape of finding `docs/languages-scoping.md` §3 records
for bit-vectors.

| Encoding | Fidelity | Size | When to prefer |
|---|---|---|---|
| **A. Refuse.** If `intsize > 63` (or any parsed literal fails to fit), emit `E_UNSUPPORTED_CONSTRUCT` and translate nothing. | n/a — no translation is produced, so no `Fidelity` value is claimed | — | **~~The default until §5's `LIT_BIGINT` lands.~~ No longer needed: §4.6.** A recorded failure is the honest outcome and it is what `intsize=` exists to enable. The evaluation counts it under `E_UNSUPPORTED_CONSTRUCT`, which `include/somtparser/translation/diagnostic.h:17-19` defines as "our coverage is thin — an engineering problem", the correct bucket. |
| **B. Saturate** oversized coefficients at `±LLONG_MAX`. | `sound = false` **and** `complete = false`; `preserves_optimum = false`. No `Bound` describes it — the distortion is not a limit on a parameter. | O(1) | **Never.** Listed only to be rejected: it silently answers a different arithmetic question and no `Fidelity` value in `include/somtparser/translation/fidelity.h` can express it. |
| **C. Bit-blast** the constraint into single-bit variables and re-encode the sum. | `equisat()` | `O(n · log₂ Σ|a_i|)` new variables | Only once a bit-vector `Sort` exists (cluster F, Plan 4 per `docs/languages-scoping.md` §4.2). Not available to Plan 2. |
| **D. Carry the decimal string**, lowered through `mkConstInt(const std::string&)`. | `exact()` | O(1) | **Done, 2026-08-12 — but as `LIT_INT` and not as a new kind. See §4.6 for why.** |

### 4.2 Boolean variables inside arithmetic, and the objective's shape

**The gap.** `Hir::Op::MUL`/`ADD` over `SortKind::BOOL` arguments is meaningless: `widen()`
(`src/hir/hir.cpp`) returns `BOOL` when every argument is `BOOL`, and the lowering
would hand `parser_->mkMul` a Boolean node. OPB's variables are Boolean but every
constraint is arithmetic over them.

- **Chosen encoding**: declare each pseudo-Boolean variable as `INT` with bounds `[0,1]`.
  `hir_to_parser.cpp:144-155` emits those bounds as two assertions, so the domain is
  enforced. `Fidelity::exact()`, no size cost beyond the two bound assertions per variable.
  Downside: the model reaches the solver as QF_LIA rather than propositional SAT, which is
  a materially different fragment — and measuring exactly that difference is the project's
  research question, so it is a result rather than a defect.
- **Alternative**: keep variables `BOOL` and encode each PB constraint propositionally
  (§4.3's option C). This is the encoding axis worth an experiment, and it is the *first*
  place in cluster B where a real encoding choice exists.

**The objective.** `omt_emitter.cpp:38-44` renders an objective term only when it is an
`IDENT` or a `LIT_INT`, and refuses anything else with `E_UNSUPPORTED_CONSTRUCT`. An OPB
objective is a linear sum, so it can never be emitted directly. Encoding: one fresh `INT`
variable `obj`, one hard constraint `obj = Σ a_i t_i`, and `Objective{kind, mkIdent("obj")}`.

- Fidelity `equisat()` — one auxiliary variable, both directions preserved, and because
  the defining constraint is an equality the optimum is preserved exactly.
- Size: `+1` variable, `+1` constraint of the objective's own length.
- This is a workaround for a limitation of the emitter, not of the format. §5 records the
  alternative: teach `termText` to render an arbitrary lowered `DAGNode`, which it can
  already reach through `lowered.parser()->toString(...)`.

Note also that `HirToParser::lower` does not lower objectives at all — it records
`num_objectives` into `Stats` (`hir_to_parser.cpp:182`) and leaves emission entirely to
the text-level `omt_emitter`. Any claim that "`Objective` already exists" must be read as
"the struct exists", not "the path exists".

### 4.3 Non-linear OPB: products of literals

A term `a l₁ l₂ … l_k` is a coefficient times a *conjunction*. Over an instance,
`#product=` gives the number of distinct products `P` and `sizeproduct=` the total literal
count across them, `S`.

| Encoding | Construction | Fidelity | Size | When to prefer |
|---|---|---|---|---|
| **A. Product variable (linearisation)** | one fresh `INT` `p ∈ [0,1]` per distinct product, with `p ≤ l_j` for each `j` and `p ≥ Σ_j l_j − (k−1)`. This is exactly the transformation the competition's own parsers perform, and the linearised factorisation example in *General OPB Format* §3.1.2 shows its output. | `equisat()` | `+P` variables, `+S + P` constraints | **Default.** Keeps the model linear, so `isNonlinearOperation` never fires and the instance stays in QF_LIA. The header hints exist to size exactly this. |
| **B. Keep the product** | `mkOp(MUL, {mkInt(a), l₁, …, l_k})` | `exact()` | O(1) | Semantically the cleanest. But `isNonlinearOperation` (`src/hir/hir.cpp`) counts ≥ 2 non-constant factors and sets `feat::nonlinear()`, so the whole instance is routed as non-linear integer arithmetic. Prefer only when the experiment is specifically about NIA. |
| **C. Boolean AND + propositional PB encoding** | variables stay `BOOL`; `p ↔ AND(l₁ … l_k)` via `mkOp(AND, …)`, and each PB constraint gets a propositional encoding (sequential weighted counter, BDD, or adder network) | `equisat()` | sequential counter / BDD: `O(n · d)` variables and constraints per constraint of `n` terms and degree `d`; adder: `O(n log Σ|a_i|)` | When the point of the experiment is SAT-vs-SMT on the same instance. The `O(n · d)` factor is pseudo-polynomial in the *degree*, so it is unusable on big-integer instances — which is why the corpus's integer-size stratification matters here too. |

Note the asymmetry: option A leaves the *products* linear but the *coefficients* still
arbitrary-precision, so §4.1 applies independently.

### 4.4 WBO's top cost `T`

`T` is a hard admissibility bound (§2.4), and there is no field in `Hir::Constraint` or
`Hir::Objective` for it.

| Encoding | Construction | Fidelity | Size | When to prefer |
|---|---|---|---|---|
| **A. Relaxation variables + threshold constraint** | fresh `INT` `r_i ∈ [0,1]` per soft constraint; replace `[c_i] C_i` with the hard constraint `C_i ∨ (r_i = 1)`; add the hard constraint `Σ c_i r_i ≤ T − 1`; add `Objective{MINIMIZE, obj}` with `obj = Σ c_i r_i` | `equisat()`; optimum preserved | `+m` variables, `+m+2` constraints for `m` soft constraints | **Default and the only complete option.** The one-sided implication is sufficient: minimisation drives `r_i` to 0 whenever `C_i` can hold. |
| **B. Native soft constraints, `T` dropped** | `Constraint{soft=true, weight=c_i}`; no threshold constraint | `overApprox()` — `sound = false`, `complete = true`, `preserves_optimum = false` | O(1) | Only when the header proves `T` vacuous: if `T > sumcost` the threshold can never bind, and then this option is `exact()` instead. *Restricted OPB Format* guarantees `T = 1 + Σ costs` for competition instances where every interpretation is admissible, so this covers most of the corpus — but it must be **checked per instance**, not assumed. |
| **C. Native soft constraints, `T` dropped, unchecked** | as B without the `sumcost` check | `overApprox()` | O(1) | **Never.** On the format document's own Example 3 it reports a cost-6 optimum where the correct answer is `s UNSATISFIABLE`. |

The direction of the loss in B/C is worth stating precisely, because it is easy to get
backwards: dropping `T` *admits* assignments the format rejects, so the translated problem
has more models. Translated-SAT no longer implies original-SAT: `sound = false`,
`complete = true`. That is `Fidelity::overApprox()`, which by design carries no `Bound`
(`include/somtparser/translation/fidelity.h:93`); the site is recorded on
`EncodingChoice::site` instead.

### 4.5 Soft constraints have a struct but no lowering

`Hir::Constraint` carries `soft`, `weight` and `group` (`include/somtparser/hir/hir.h`),
which is what `docs/languages-scoping.md` §3.2 means by "`Constraint.soft`/`weight`
already exist in HIR". But `HirToParser::lower` refuses them:

```cpp
// Historical soft-constraint refusal, before R237b; not the current lowerer.
if (c.soft) {
    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT, …
                      "cannot be lowered: no encoding for soft constraints is implemented yet", …);
    return false;
}
```

The comment there explains why it refuses rather than hardening — hardening turns "violate
at cost w" into "never violate", which can turn a satisfiable MaxSMT instance UNSAT. That
reasoning is correct and should not be weakened. The consequence for planning is simply
that **a soft-constraint lowering is real work that Plan 2 must do**, and it is not
captured by "no new HIR feature".

Two designs, and they are not equivalent:

- **Relaxation-variable encoding** (§4.4 option A). Produces a plain OMT instance with a
  linear objective. Works with any OMT backend. `equisat()`.
- **Native `assert-soft`**, delegating to the engine's existing OMT support. Preserves the
  MaxSAT structure for a solver that exploits it. Requires `HirToParser` to gain a path to
  the engine's soft-assertion builder and `omt_emitter` to gain a `maxsat` objective form.
  Potentially `exact()`.

### 4.6 `Constraint::weight` is `double`

`Hir::Constraint::weight` is declared `double weight = 1.0`
(`include/somtparser/hir/hir.h`). WBO costs are strictly positive integers of arbitrary
size. A `double` represents integers exactly only up to `2^53 ≈ 9.0 × 10^15`; beyond that,
distinct costs collide.

| Encoding | Fidelity | Notes |
|---|---|---|
| Store cost in `weight` as-is | `preserves_optimum = false` once any cost exceeds `2^53`; two soft constraints with different costs can become indistinguishable, so the reported optimum is wrong, not merely bounded | Silent. There is no diagnostic today. |
| Refuse when any cost exceeds `2^53` | no translation claimed | Honest, and cheap to implement. |
| §4.4's relaxation encoding, cost carried as a `LIT_INT` coefficient | `equisat()` up to `LLONG_MAX`, then §4.1 applies | Sidesteps `weight` entirely — the cost becomes an ordinary integer coefficient in the objective. **Recommended.** |

That last row is the practical reason to prefer the relaxation encoding even where native
soft constraints exist: it moves the weight from a `double` into the same exact-integer
path as every other coefficient.

---

## 4.6 How the unbounded-integer gap was actually closed

Option D, and **not** as `ExprKind::LIT_BIGINT`. The recommendation above named a new kind;
what landed on 2026-08-12 is a text-backed `LIT_INT`, and the difference is a design decision
worth recording rather than a detail.

**A big integer is not a different kind of literal.** SMT-LIB has one numeral syntax, and
`long long` is a limit of the `Expr::int_value` field rather than of the language. Introducing
`LIT_BIGINT` would have put a C++ limitation into the IR's *vocabulary*, and every consumer —
`typeCheck`, the lowering, `isConstant`, `isNonlinearOperation`, and every future pass — would have
had to handle two kinds forever. That is not hypothetical: `isConstant` listed `LIT_INT` and
`LIT_BOOL` and silently missed `LIT_BITVEC`, which made `(bvmul x #b10)` report as nonlinear.
One kind that some consumers know about is the shape of that bug.

So `LIT_INT` now carries the decimal text in `Expr::name`, authoritative, and `int_value` is
valid **only when the literal fits**. `Uir::Hir::fitsInt64` is how a consumer finds out, and
the two that need a machine integer — the ground `alldifferent` expansion and MiniZinc's
constant array index — ask before reading. Reading `int_value` unconditionally on a wide
literal would use a wrong number silently, which is the failure the text backing exists to
prevent.

`LIT_REAL` already worked this way, for the same reason one step over: `0.1` has no finite
binary expansion and `1/3` has no decimal one, so its value is text too. The two literals are
now consistent, and no `LIT_NUM` is needed to serve LP, MPS, WCNF and OPB.

**A checker defect surfaced doing it.** `scripts/check-doc-citations.py` decides whether a
vocabulary name exists by searching the header, and `hir.h` names `LIT_BIGINT` only to explain
why it was *not* introduced — which the search read as the introduction, and it reported four
documents as describing a landed feature as future work. The existence test now ignores
comment lines, so a name discussed in prose no longer counts as a name declared.

---

## 4.7 What building it settled

**§4.4's option was decided per instance rather than chosen once.** T is compared against the
sum of costs in unbounded arithmetic — costs are big integers by design, and summing them as
`long long` makes the comparison come out backwards on a corpus instance. When T is provably
vacuous the translation is option B and `exact()`; otherwise it is option A, which is always
correct. Neither branch needs a `Fidelity` recorded, which matters because
`Lang::ParseOutcome` still carries no `TranslationReport` and a frontend has nowhere to write
one (`minizinc.md` §3.3 records the same gap).

The boundary is where an off-by-one lives: `T = sumcost` **binds**, because the cost must be
*strictly* less than T, and `T = sumcost + 1` is the first vacuous value. The emitted bound is
`Σ c_i r_i ≤ T − 1`; writing `≤ T` would admit exactly the assignments the format rejects.

**Two gaps in the pipeline this format found**, both of the shape "a construct the engine
models and the public API narrows":

1. `Hir::Constraint::weight` is a `double`, and WBO costs are big integers. 10²³ through a
   double comes back as scientific notation, which is not a numeral and which the engine's
   builder rejects — so the *first* big-cost instance failed to translate at all. `weight_text`
   now carries the exact value, the same decision as `Expr::int_value`'s one layer down.
2. The OMT emitter could print an objective that was a bare variable or an integer literal and
   refused everything else — which made a **summed** objective unemittable, i.e. every OPB
   instance with a `min:` line and every MaxSAT cost function. Its own header comment says it
   "never re-implements printing"; the two special cases were exactly that. It now lowers the
   term and prints the node.

**`~x` and the Boolean domain are one obligation, not two.** A product of literals is a
conjunction, and over {0,1} integers that is exactly their arithmetic product — so the `[0,1]`
bounds are what make `1 x1 x2` mean what the format says. Without them the multiplication is
still well-formed and means something else. The two obligations are tested together for that
reason.

---

## 5. New HIR surface this format forces

| Item | Demanded by | Shared with |
|---|---|---|
| ~~**`ExprKind::LIT_BIGINT`**~~ **landed 2026-08-12 as text-backed `LIT_INT`** (§4.6) | §4.1 — arbitrary-precision coefficients, degrees and soft costs; the format document's own example exceeds `long long` | WCNF, LP, MPS — and `LIT_REAL` already carries decimals and exact rationals as text for the same reason, so all four are served without a `LIT_NUM`. Cluster B in `docs/languages-scoping.md` §3.1 assumed none of them needed anything. |
| **An exact-integer `Constraint::weight`** replacing `double` | §4.6 | WCNF, and every future MaxSAT-shaped language. Not shared with LP/MPS, which have no soft constraints. |
| **A soft-constraint lowering** in `HirToParser` (relaxation encoding and/or native `assert-soft`) | §4.5 — `hir_to_parser.cpp:163-172` refuses `soft` today | WCNF. This is a pass/lowering item, not a HIR struct item, which is why `docs/languages-scoping.md` §3.1's "new HIR feature" column does not catch it. |
| **An objective term richer than `IDENT`/`LIT_INT`** in `omt_emitter::termText` | §4.2 — every OPB/PBO objective is a linear sum | LP, MPS, WCNF. Avoidable with the auxiliary-variable workaround, at `+1` variable and `+1` constraint per objective. |
| *(not required)* a top-cost field | §4.4 encodes `T` as an ordinary constraint | — |
| *(not required)* non-linear surface | §4.3 option A linearises; option B uses the existing `Op::MUL` | — |

Nothing here needs a new `ExprKind` for structure, a new `Sort`, quantifiers, arrays or a
`TransitionSystem`. The cluster-B classification is right about the *shape* of the IR and
wrong about the *domain of its literals* and the *state of its lowering*.

---

## 6. Fidelity summary

**Exact (`Fidelity::exact()`)**

- Linear PBS instances whose every coefficient and degree fits `long long`, with variables
  encoded as `INT ∈ [0,1]`.
- All eight relational operators of the general format, including `!=` — which needs no
  disjunctive trick in SMT.
- Comments, header hints, `soft: ;` with `T = ∞`.
- WBO instances whose `T` is provably vacuous (`T > sumcost`, checkable from the header).

**Equisatisfiable (`Fidelity::equisat()`) — auxiliary variables, both directions preserved**

- Any objective (auxiliary `obj` variable, §4.2).
- Non-linear products under the linearising encoding (§4.3 A).
- WBO under the relaxation encoding (§4.4 A), including the top-cost threshold.
- Propositional PB encodings (§4.3 C), with the size caveats stated there.

**Inherently lossy**

- Nothing in OPB/WBO is inherently lossy against an SMT/OMT target. Every construct has an
  exact or equisatisfiable encoding *given* an unbounded integer literal. The losses in §4
  are all artefacts of the current HIR's `long long` and `double` fields, not of the source
  language — which makes them fixable, and makes fixing them the right call rather than
  documenting a permanent approximation.
- The two options that are genuinely lossy — saturation (§4.1 B) and dropping an
  unchecked `T` (§4.4 C) — are both recommended against, and neither corresponds to a
  `Fidelity::Bound`: saturation is not a limit on a parameter, and over-approximation
  carries no `Bound` by design.

**Out of scope**

- Model counting and enumeration (`models:`, `project:`, `count:`, `enum:`) — a different
  question, per `docs/languages-scoping.md` §6.3's treatment of the Model Counting
  Competition. `E_UNSUPPORTED_CONSTRUCT`.

---

## 7. References

**Format specifications**

1. O. Roussel, *General OPB Format*, `$Rev: 4524$`, 2024-03-11.
   <https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf>
2. O. Roussel, *Restricted OPB Format in Use in the PB Competitions*, `$Rev: 4524$`,
   2024-03-11. <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf>
3. O. Roussel and V. Manquinho, *Input/Output Format and Solver Requirements for the
   Competitions of Pseudo-Boolean Solvers*, `$Rev: 2324$`, 2016-01-14.
   <https://www.cril.univ-artois.fr/PB16/format.pdf>
4. OPBDP, the origin of the OPB format (its README). <http://opbdp.sourceforge.net/>

**Competitions and corpora**

5. Pseudo-Boolean Competition 2024. <https://www.cril.univ-artois.fr/PB24/>
6. Pseudo-Boolean Competition 2016. <https://www.cril.univ-artois.fr/PB16/>
7. Instance archives: `https://www.cril.univ-artois.fr/PB24/benchs/selected-PB24.tar`
   (255 MiB), `https://www.cril.univ-artois.fr/benchs/SampleByIntSize.tar` (128 MiB),
   `normalized-PB24.tar` (2.5 GiB). Instance counts and licence: **not found**.

**Semantics**

8. V. Manquinho, J. Marques-Silva and J. Planes, *Algorithms for Weighted Boolean
   Optimization*, SAT 2009, LNCS, pp. 495–508 — the source of the WBO definition quoted in
   both format documents.

**This project**

9. `docs/languages-scoping.md` §3.1 (cluster B), §3.2 (cost 0.4×), §4 (Plan 2), §6.3
   (why model counting is declined).
10. `docs/superpowers/specs/2026-08-10-languages-design.md` §4.1 (the `Fidelity` lattice
    and why over-approximation carries no `Bound`), §4.7 (HIR; the note that OPB/WBO and
    WCNF map to "maxsat + soft weights").
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `src/hir/hir.cpp`, `src/lowering/hir_to_parser.cpp`, `src/lowering/omt_emitter.cpp` —
    the code every claim in §3–§5 is checked against.
