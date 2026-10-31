# WCNF — weighted and partial MaxSAT

The parser shares immutable positive and negative literal nodes across clauses.
Repeated soft clauses remain separate contributions to the objective, with their
exact decimal weights and original constraint locations preserved. An integer
literal whose magnitude exceeds the signed 64-bit index range is diagnosed
before taking its absolute value.

**Date**: 2026-08-11
**Status**: **implemented** (`languages/wcnf/`, `test/languages/test_wcnf.cpp`). Written
document-first: every obligation in the block below predates the code, and each is a fixture
in `languages/wcnf/instances`.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster B, §3.2 (cost 0.3×,
"DIMACS + per-clause weight; `Constraint.soft`/`weight` already exist in HIR"), §4 (Plan 2).

**Headline result of the audit in §4**: the struct fields do exist, so the *shape* half of
the cluster-B claim holds. Two things it does not cover: `Constraint::weight` is declared
`double`, which cannot represent MaxSAT weights exactly across their documented range
(§4.2); and `HirToParser` **refuses** every constraint with `soft = true` rather than
lowering it (§4.3). WCNF is therefore the first language in the batch whose translation
requires new lowering work, even though it requires no new HIR struct.


<!-- implicit-constraints:
  old format, a clause whose weight >= top => a HARD constraint, not a soft one at that weight (§2)
  new format, a clause with no leading weight => hard; the absence of a weight is the declaration (§2)
  soft clauses are jointly optimised => the objective is the sum of violated weights, which no single clause states (§3)
-->
---

## 1. What the format is

WCNF extends DIMACS CNF with per-clause weights. It is the input language of the
**MaxSAT Evaluation**, the annual assessment of MaxSAT solvers held with the SAT
conference. The problem: satisfy every hard clause and minimise the total weight of
falsified soft clauses.

The format exists in **two incompatible revisions**, and the split is the single most
important thing about it for a parser.

### Standard documents

| Revision | Normative source | Notes |
|---|---|---|
| **New (2022 →)** | MaxSAT Evaluation 2022 rules, <https://maxsat-evaluations.github.io/2022/rules.html> — "Note that the input format is changed for 2022." | No `p` line; `h` marks hard clauses. |
| **New, with the bounds restated** | MaxSAT Evaluation 2023 rules, <https://maxsat-evaluations.github.io/2023/rules.html> | Adds the explicit statement that the **sum** of the weights must be less than `2^64 − 1`; comment lines start with `c `. |
| **Old (≤ 2021)** | the `p wcnf nbvar nbclauses top` header, described by contrast in the 2022 rules page above | Still the format of every archived pre-2022 instance, so a frontend that wants the historical corpus needs both readers. |

The evaluation portal <https://maxsat-evaluations.github.io/> lists editions **2017
through 2026**, with 2016-and-earlier archived separately at <http://www.maxsat.udl.cat>.
The format has not changed again since 2022: the 2023 rules restate the 2022 description
verbatim plus the sum bound.

### Tracks, reference implementations, corpus

Tracks are **exact** (complete solvers, ranked by instances solved optimally) and
**anytime** (incomplete solvers, ranked by an anytime score), each split weighted /
unweighted, plus a **special incremental track introduced in 2022**.

EvalMaxSAT, UWrMaxSat, CASHWMaxSAT and Open-WBO are the commonly-cited open-source
solvers. **Which won the most recent editions, and their current versions and licences,
were not confirmed in this pass** — pin one before differential testing begins.

Corpus: the evaluation's benchmark collection, linked from each edition's pages.
**Instance counts are not published in advance by design** — the 2023 rules state that the
benchmark set "will be revealed only after the results from the evaluation are presented
at the SAT 2023 conference", and that instances are selected by bucketing similar
instances and drawing randomly from each bucket. Per-edition archives are published
afterwards. **Licence terms: not found.**

---

## 2. Semantics — what a file means

### 2.1 The new format (2022 onwards)

```
c a comment
h 1 2 3 4 0
1 -3 -5 6 7 0
6 -1 -2 0
4 1 6 -7 0
```

- **No problem line.** The 2022 rules give the reason directly: "The p-line is a source of
  many problems when constructing benchmark files." A reader must therefore discover the
  variable count from the clauses.
- **Hard clauses**: "Hard clauses are declared by `h` instead of a weight."
- **Soft clauses**: "We associate a weight with each *soft* clause, which is the first
  integer in the soft clause."
- **Clause body**: unchanged from DIMACS — "Variables as indexed with positive integers. A
  clause is a listing of variables indices, with `-` used to denote negation. `0` marks the
  end of the declaration of a clause."
- **Comments** begin with `c `.

### 2.2 The old format (≤ 2021)

```
p wcnf 7 4 12
12 1 2 3 4 0
1 -3 -5 6 7 0
6 -1 -2 0
4 1 6 -7 0
```

The header is `p wcnf <nbvar> <nbclauses> <top>`. Every clause carries a leading weight,
and **a clause whose weight is greater than or equal to `top` is a hard clause**. In the
example above `top = 12` and the first clause's weight is 12, so it is hard — the same
instance as §2.1's.

Related headers seen in pre-2022 corpora: `p wcnf <nbvar> <nbclauses>` without a `top`
field (weighted MaxSAT, no hard clauses) and plain `p cnf` (unweighted MaxSAT, every
clause soft with weight 1).

**`top` in WCNF is a marker, not a threshold.** This is worth stating explicitly because
WCNF's sibling format WBO uses a superficially identical word for something else: WBO's
`soft: T ;` is a hard *admissibility bound* — an assignment whose cost reaches `T` is not a
solution at all, and the instance can be UNSATISFIABLE even though a minimum-cost
assignment exists (`opb-wbo.md` §2.4). WCNF's `top` says only "clauses this heavy are
hard". Translating either one with the other's semantics changes the answer.

### 2.3 What a solution is, and what the objective is

An assignment satisfying **every hard clause**, minimising **the sum of the weights of the
falsified soft clauses**. If the hard clauses are jointly unsatisfiable, the instance is
UNSATISFIABLE and there is no optimum.

The objective is therefore **implicit**: it appears nowhere in the file and must be
synthesised by the frontend. `docs/superpowers/specs/2026-08-10-languages-design.md` §4.7
already states the intended mapping — "OPB/WBO 与 WCNF 映射到 maxsat + soft weights" —
i.e. `Constraint::soft`/`weight` plus a MaxSAT-shaped `Objective`.

### 2.4 Numeric semantics

Exact integers, and the documented ranges are precise enough to check against the HIR:

| Quantity | Documented range | Source |
|---|---|---|
| a soft clause weight | `≥ 1` and `< 2^63` | MaxSAT Evaluation 2022 and 2023 rules |
| the sum of all weights | `< 2^64 − 1` | MaxSAT Evaluation 2023 rules |
| hard clauses | no weight (new format); `≥ top` (old format) | both |

Two consequences, and they pull in opposite directions:

- An individual weight **fits `long long`** (`2^63 − 1 = LLONG_MAX`), so `Hir::mkInt` can
  carry any legal weight as a coefficient. Unlike OPB (`opb-wbo.md` §4.1), WCNF has no
  arbitrary-precision problem.
- An individual weight **does not fit a `double` exactly** above `2^53`. See §4.2.
- The *sum* can exceed `long long` — `2^64 − 1` is twice `LLONG_MAX`. This does not affect
  the HIR, which stores only the individual coefficients; it affects whoever accumulates
  them, and in this project that is the GMP-backed `Integer` in
  `include/somtparser/ir/number.h`. Stated so the claim is not over-generalised in either
  direction.

Weight `0` is illegal in the new format (weights are "greater than or equal to 1"). Some
older tooling emitted it; treat it as `E_PARSE`, or as a vacuous soft clause under
`ParseOptions::strict == false`, but do not silently keep it as a soft constraint whose
violation is free.

The expanded and packed frontends additionally accept positive decimal weights
and `top` markers beyond the competition's numeric range. This is an exact-integer
extension, not a claim that those larger values meet the competition rules. Both
paths normalize leading zeros, compare `top` using decimal text, and preserve
soft costs in the HIR's authoritative `weight_text` field or packed weight pool.
Zero, signs, fractional values, and exponent notation remain invalid weights.

### 2.5 Output, for differential testing

`s OPTIMUM FOUND` / `s UNSATISFIABLE` / `s UNKNOWN`, `o <cost>` lines reporting improving
solution costs, and a `v` line giving the assignment. The 2022 rules describe the `v` line
in literal form ("A literal is denoted by an integer that identifies the variable and the
negation of a literal is denoted by a minus sign immediately followed by the integer"),
e.g. `v -1 2 3 -4 …`. **A compact 0/1-string `v` line is also in circulation from earlier
evaluations; which form the most recent editions require was not re-confirmed in this
pass** — check the target edition's rules page before writing a comparison harness.

---

## 2.6 What building it settled

**Historical implementation snapshot.** This subsection records the earlier implementation milestone; its description of what had to land is not a claim about the current R237b source.

**The two formats produce byte-identical output.** `wcnf.md` §2.2 says the old-format example
"is hard — the same instance as §2.1's", and the test asserts exactly that: the same file in
both spellings translates to the same script, character for character. That is a stronger
claim than counting clauses, and it is what a misreading of `top` breaks *without breaking
either file on its own*.

**Three things had to land before the format was translatable at all**, and each was a
construct the engine modelled and the public API could not reach:

1. `Parser::assertSoft` — soft assertions were reachable only through `parseAssertSoft`, which
   reads from the token stream.
2. `dumpSMT2` emitting `(assert-soft …)` — it emitted nothing, so a MaxSAT problem read
   through this library came back a **plain SAT problem**, with the optimisation objective
   silently gone.
3. `PassManager::validate` erasing `feat::softConstraint()`, the way it erases
   `feat::quantifier()`. Both lower natively now; before (1) and (2) this erase would have
   been *wrong*, waving a model through to fail one layer down.

The three belong together and landed together. Until they did, `HirToParser` refusing a soft
constraint was correct: hardening one changes the problem from "violate this at cost *w*" to
"never violate this", which can turn a satisfiable MaxSAT instance UNSAT, and a wrong answer
reported as success is worse than a recorded failure.

**Three tests inverted**, which is the intended lifecycle rather than breakage — they pinned
the refusal, and the refusal was scaffolding. What survives each inversion is the property the
refusal protected: the constraint must not arrive as a *hard* one. "It translated" alone would
pass for a frontend that hardened it. One of them, `test_uir_passmanager`'s
unsupported-construct-versus-misconfigured-pipeline contrast, kept its structure by moving to
a feature that still has no native lowering, rather than being deleted with the scaffold.

---

### 2.7 Packed streaming backend

The default `wcnf` frontend keeps the established expanded HIR, including binary-clique
compression, so existing callers that inspect `Translation::parser()` retain that behavior.
For inputs whose per-variable/per-clause HIR expansion is too large, callers can opt into the
packed Boolean representation with the language parse option `packed=1` (for example, the
Python API's `options={"packed": "1"}`). That path stores variable intervals and clause
pools compactly and streams SMT-LIB output. Such a successful translation has no materialized
`Parser`; `hasParser()` is false, `parser()` throws `std::logic_error`, and callers should use
`writeSmt2()` or `toSmt2()`. `packed=0` and an omitted option select the established frontend.

Both modes preserve hard/soft status and decimal weights. The packed mode also keeps the
weight text exact instead of converting through `double`; its direct SMT writer handles empty
clauses as `(or)` and rejects malformed ranges before emission.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.
Everything DIMACS CNF contributes is covered in `dimacs-cnf.md` §3 and not repeated; this
table covers what WCNF adds.

**Historical mapping snapshot (pre-R237b).** In particular, the “no lowering” and
“cannot render” entries below record the earlier implementation and should not be read as
current behavior. The current WCNF exact-weight path is summarized in §4.2.

| Construct | HIR representation | New HIR surface required | Fidelity | Notes |
|---|---|---|---|---|
| `c …` comment | dropped | none | `exact()` | |
| variable / literal / clause body | as `dimacs-cnf.md` §3 | none | `exact()` | Includes the empty-clause trap: `mkBool(false)`, never `mkOp(OR, {})` — `src/hir/hir.cpp`. |
| **new format** `p` line | absent by design | none | `exact()` | Variable count is derived from the clauses. |
| **old format** `p wcnf V C top` | not represented; `top` drives the hard/soft split | none | `exact()` | |
| **new format** `h <clause>` | `Constraint{formula, soft = false}` | none | `exact()` | Lowered by `hir_to_parser.cpp:173-177` as an ordinary assertion. |
| **new format** `<w> <clause>` | `Constraint{formula, soft = true, weight = w}` | none in the struct; **no lowering exists** | see §4.2, §4.3 | |
| **old format** clause with weight `≥ top` | `Constraint{formula, soft = false}` | none | `exact()` | The weight is discarded, which is correct: it was only the hard marker. |
| **old format** clause with weight `w < top` | `Constraint{formula, soft = true, weight = w}` | none in the struct; **no lowering exists** | see §4.2, §4.3 | |
| old-format `p wcnf V C` (no `top`) | every clause soft | none | `exact()` | |
| old-format `p cnf` read as MaxSAT | every clause soft with weight 1 | none | `exact()` | The same bytes are a satisfiability instance under `dimacs-cnf.md`; the *problem* differs, so this must be an explicit frontend selection, not a sniff. |
| empty soft clause (`<w> 0`) | `Constraint{formula = mkBool(false), soft = true, weight = w}` | none | `exact()` | Always falsified: contributes `w` to every solution's cost. Legal and occasionally used to encode a constant offset. Under §4.4's encoding its relaxation variable is forced to 1. |
| empty hard clause (`h 0`) | `Constraint{formula = mkBool(false)}` | none | `exact()` | Instance is UNSATISFIABLE. |
| the implicit objective | synthesised — see §4.4 | none in the struct; `omt_emitter` cannot render it (§4.5) | `equisat()` | `Objective{MINIMIZE, …}`; `Hir::Objective` exists (`hir.h:981-986`). |
| `Constraint::group` | unused | none | — | WCNF has no clause groups. Group-MaxSAT is a research variant, not part of the evaluation format. |

---

## 4. Semantic gaps and encoding choices

### 4.1 What is genuinely exact

Everything structural. Hard clauses, soft clauses, the hard/soft split under both header
conventions, the empty clause in either role, and the whole DIMACS substrate map exactly.
WCNF adds no construct that resists translation.

The gaps below are all about **weights and the objective**, and all four are properties of
the current HIR and lowering rather than of the source language.

### 4.2 Exact integer weights in the current WCNF path

A `double` cannot distinguish every integer above `2^53`. The current WCNF parser checks and stores each positive integer weight (`languages/wcnf/src/wcnf.cpp:354-362`).
It also stores the exact integer value as decimal text in `weight_text` (`languages/wcnf/src/wcnf.cpp:588-591`).
The HIR field `weight_text` carries that value (`include/somtparser/hir/hir.h`), and lowering emits it as an
integer literal through `mkConstInt(c.weight_text)` in [HIR lowering](../../src/lowering/hir_to_parser.cpp). Thus this WCNF path does not
round legal individual weights through `double`. Other frontends that populate only the
double field remain subject to the `2^53` exact-integer limit; do not generalise the WCNF
preservation mechanism to those paths.

**Historical design note.** Sections 4.3–4.5 and the corresponding implementation claims
in §§5–6 preserve a pre-R237b analysis. Their refusal excerpt and statements that soft
constraints cannot be lowered or objectives cannot be rendered describe that earlier
source state, not the current R237b implementation. Treat those sections as historical
rationale; they are not claims about current behavior.

### 4.3 `HirToParser` refuses soft constraints outright

```cpp
// Historical soft-constraint refusal, before R237b; not the current lowerer.
if (c.soft) {
    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                      "soft constraint (weight " + std::to_string(c.weight) + …
                      ") cannot be lowered: no encoding for soft constraints is "
                      "implemented yet", c.loc);
    return false;
}
```

The refusal is correct — the comment above it explains that asserting a soft constraint
would turn "violate this at cost w" into "never violate this", which can turn a satisfiable
MaxSMT instance UNSAT — and it should not be weakened.

The planning consequence is that **a WCNF translation cannot complete today**, for any
instance with a soft clause, which is every instance. `docs/languages-scoping.md` §3.2's
0.3× estimate ("`Constraint.soft`/`weight` already exist in HIR") measures the parser and
not this. The missing work is a lowering, and there are two designs:

| Design | Fidelity | Cost | Notes |
|---|---|---|---|
| **Relaxation encoding** (§4.4) | `equisat()` | one pass over `constraints`; no engine changes | Produces a plain OMT instance with a linear objective. Works against any OMT backend, including the `SmtLib2025`, `Z3` and `OptiMathSAT` dialects `omt_emitter.cpp:89-101` already emits. |
| **Native soft assertion**, delegating to the engine's existing OMT/`assert-soft` support (`src/frontend/opt_parser.cpp`) | potentially `exact()` | `HirToParser` needs a path to the engine's soft-assertion builder; `omt_emitter` needs a MaxSAT objective form | Preserves the MaxSAT structure for a solver that exploits it, which is the more interesting experiment. Requires §4.2 D so the weight survives. |

These are not alternatives to choose between once: they are two encodings of the same
construct, which is exactly what `TranslationReport::choices()` and `EncodingChoice` exist
to record.

### 4.4 Synthesising the objective: the relaxation encoding

For each soft clause `C_i` with weight `w_i`:

1. add `VarDecl{r_i, Sort::integer(), lower = mkInt(0), upper = mkInt(1)}`;
2. replace the soft constraint with the **hard** constraint
   `mkOp(OR, {C_i, mkOp(EQ, {mkIdent(r_i), mkInt(1)})})`;
3. add `VarDecl{obj, Sort::integer()}` and the hard constraint
   `mkOp(EQ, {mkIdent(obj), mkOp(ADD, {mkOp(MUL, {mkInt(w_i), mkIdent(r_i)}) …})})`;
4. add `Objective{ObjKind::MINIMIZE, mkIdent(obj)}`.

- **Fidelity `equisat()`.** The implication is one-sided — `r_i = 1` permits `C_i` to be
  false but does not force it — and that is sufficient, because minimisation drives every
  `r_i` to 0 whenever `C_i` can hold. The optimum is preserved exactly.
- **Size**: `+m + 1` variables and `+m + 1` constraints for `m` soft clauses; the
  objective-defining constraint has `m` terms. Linear in the input.
- **Non-linearity check**: each product `w_i · r_i` has exactly one non-constant factor, so
  `hasNonlinearMul` (`src/hir/hir.cpp`) does **not** set `feat::nonlinear()`. The
  instance stays in QF_LIA.
- **Why `r_i` is `INT` and not `BOOL`**: it is summed. `widen()` (`src/hir/hir.cpp`)
  returns `BOOL` for an all-`BOOL` argument list, and `Parser::mkMul` has no meaning on a
  Boolean node. The same reasoning applies to OPB's variables (`opb-wbo.md` §4.2).
- **Unweighted instances** are the special case `w_i = 1`, where the objective counts
  falsified soft clauses. No separate encoding is needed.

**Degradation if the objective is dropped** (e.g. `OmtDialect::None`): the relaxed model is
satisfied by setting every `r_i = 1`, so it is a pure over-approximation of the original
MaxSAT problem — `sound = false`, `complete = true`, `preserves_optimum = false`, i.e.
`Fidelity::overApprox()`. Because that is easy to reach by configuration rather than by
choice, `omtDialectName`'s own comment (`src/lowering/omt_emitter.cpp:61-64`) is worth
heeding: a dropped objective must be visible in the report, not inferred.

### 4.5 Objective terms use the shared target printer

The earlier emitter accepted only an identifier or an integer literal. That
restriction is historical: `termText` now lowers any supported objective term
and prints the resulting target node (`src/lowering/omt_emitter.cpp`, `termText`).
The sum in §4.4 therefore does not need an auxiliary objective identifier solely
to work around an emitter restriction. A frontend may still introduce a cost
variable for its own encoding; that choice must retain the complete cost relation.

Native `assert-soft` groups also count as effective minimization objectives.
This metadata does not introduce a hard cost threshold: WCNF's `top` remains a
weight marker, whereas a nonvacuous WBO `soft: T` remains a strict admissibility
bound. `test/languages/test_pb_cross_format.cpp` checks that distinction as well
as source/target objective directions and the two emission forms.

---

## 5. New HIR surface this format forces

| Item | Demanded by | Shared with |
|---|---|---|
| **A soft-constraint lowering** in `HirToParser` — relaxation encoding, native `assert-soft`, or both as recorded `EncodingChoice`s | §4.3; `hir_to_parser.cpp:163-172` refuses `soft` today, so no WCNF instance can be translated at all | OPB/WBO (`opb-wbo.md` §4.5). Not a HIR struct change, which is exactly why `docs/languages-scoping.md` §3.1's "new HIR feature" column does not catch it. |
| **An exact-integer `Constraint::weight`** replacing `double` | §4.2; weights run to `2^63` while `double` is exact to `2^53` | OPB/WBO. Avoidable by §4.4's encoding, which routes the weight through a `LIT_INT` coefficient instead — so this is required only if native soft constraints are supported. |
| **An objective term richer than `IDENT`/`LIT_INT`** in `omt_emitter::termText` | §4.5; a MaxSAT objective is a weighted sum | OPB/WBO, LP, MPS. Avoidable at `+1` variable and `+1` constraint. |
| *(not required)* a big-integer literal | §2.4 — weights fit `long long` | OPB, LP and MPS do need one (`opb-wbo.md` §4.1, `lp.md` §4.1); WCNF does not. |
| *(not required)* new `ExprKind`, `Sort`, or pass | — | — |

A shared helper worth extracting alongside `dimacs-cnf.md` §5's: WCNF, DIMACS and QDIMACS
all read the same line-oriented clause body, and the literal-interning discipline
`dimacs-cnf.md` §4.4 recommends applies unchanged.

---

## 6. Fidelity summary

**Exact (`Fidelity::exact()`)**

- The whole DIMACS substrate: variables, literals, clauses, empty clauses, comments.
- The hard/soft split under both the new (`h`) and old (`weight ≥ top`) conventions,
  including the discarding of the old format's hard-clause weights.
- Every soft clause whose weight is at most `2^53`, when carried in `Constraint::weight`;
  every legal weight, when carried as a `LIT_INT` coefficient under §4.4.

**Equisatisfiable (`Fidelity::equisat()`) — auxiliary variables, both directions and the
optimum preserved**

- The synthesised objective under §4.4's relaxation encoding, including the `obj` variable
  forced by `omt_emitter`'s restriction.

**Inherently lossy**

- Nothing in WCNF is inherently lossy against an SMT/OMT target. The one loss that arises
  today — weights above `2^53` rounded by a `double` field (§4.2) — is a property of the
  current HIR, is silent, is not describable by any `Fidelity::Bound`, and is removed
  entirely by the recommended encoding.

**Currently untranslatable**

- Every instance, until §4.3's lowering exists: `hir_to_parser.cpp:163-172` fails any model
  containing a soft constraint with `E_UNSUPPORTED_CONSTRUCT`. This is the correct
  behaviour for today's code and the concrete definition of what Plan 2 owes WCNF.

---

## 7. References

**Format specification**

1. MaxSAT Evaluation 2022, rules and input/output format — the revision that removed the
   `p` line and introduced `h` for hard clauses.
   <https://maxsat-evaluations.github.io/2022/rules.html>
2. MaxSAT Evaluation 2023, rules — restates the format and adds the sum-of-weights bound
   `< 2^64 − 1`. <https://maxsat-evaluations.github.io/2023/rules.html>
3. MaxSAT Evaluation portal, editions 2017–2026.
   <https://maxsat-evaluations.github.io/>
4. MaxSAT Evaluations 2016 and earlier. <http://www.maxsat.udl.cat>
5. The DIMACS substrate: *Satisfiability: Suggested Format*, 1993-05-08.
   <http://archive.dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.tex>

**Corpus and solvers**

6. Benchmark archives are published per edition after the results are presented; the 2023
   rules state the selection method (bucketing by similarity, random draw per bucket) and
   that the set is revealed only afterwards. **Instance counts and licence: not found.**
7. EvalMaxSAT, UWrMaxSat, CASHWMaxSAT, Open-WBO — candidate differential-testing oracles;
   **versions, repositories and recent winners not confirmed in this pass.**

**This project**

8. `docs/languages-scoping.md` §3.1 (cluster B), §3.2 (cost 0.3×), §4 (Plan 2).
9. `docs/superpowers/specs/2026-08-10-languages-design.md` §4.1 (the `Fidelity` lattice and
   why over-approximation carries no `Bound`), §4.7 (HIR; "WCNF 映射到 maxsat + soft
   weights").
10. `opb-wbo.md` §2.4 (WBO's `top` versus WCNF's, the two must not be conflated), §4.4–§4.6
    (the same relaxation encoding, and the same `double`/objective gaps seen from the PB
    side); `dimacs-cnf.md` §3–§4 (the shared clause substrate).
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`, `src/hir/hir.cpp`,
    `src/lowering/hir_to_parser.cpp`, `src/lowering/omt_emitter.cpp`,
    `include/somtparser/ir/number.h`.
