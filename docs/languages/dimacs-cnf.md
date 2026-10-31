# DIMACS CNF — propositional satisfiability

**Date**: 2026-08-11
**Status**: **implemented** (`languages/dimacs/`, `test/languages/test_dimacs.cpp`, and
`test/languages/test_sat_cross_format.cpp` for the half that only exists between formats).
Written document-first: every obligation in the block below predates the code, and each is now
a fixture in `languages/dimacs/instances`.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster B, §3.2 (cost 0.2×, "cheapest
of all 22"), §4 (Plan 2).

**Headline result of the audit in §4**: for DIMACS CNF the cluster-B claim is **correct
without qualification** — this is the one format in the batch that needs no new HIR
surface, no new pass, and no encoding choice. That makes it the control case against which
§4 of `lp.md`, `mps.md`, `wcnf.md` and `opb-wbo.md` state their exceptions. The only
issues DIMACS raises are one construction edge case (§4.1) and a memory-footprint concern
that is engineering, not fidelity (§4.4).


<!-- implicit-constraints:
  a variable in 1..VARIABLES occurring in no clause => still a VarDecl; the file's vocabulary is the header's, not the clauses' (§3)
  the empty clause `0` => mkBool(false), never mkOp(OR, {}) which throws (§4.1)
  no objective is present => objectives stays empty and preserves_optimum is vacuously true, not "verified preserved" (§2.2)
-->
---

## 1. What the format is

DIMACS CNF is the input language of propositional SAT solvers: a conjunction of clauses
over Boolean variables identified by positive integers. It has been the SAT community's
lingua franca since the Second DIMACS Implementation Challenge (1992–93) and is the input
format of every SAT Competition since.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| *Satisfiability: Suggested Format*, DIMACS (Second DIMACS Challenge) | "Last revision: May 8, 1993" | <http://archive.dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.tex> (also `satformat.ps`, `satformat.dvi` in the same directory) |
| SAT Competition 2025 | competition rules and output requirements, results announced 2025-08-15 | <https://satcompetition.github.io/2025/> |

The 1993 document is the only thing resembling a formal specification, and it is
**"suggested"** by its own title. What solvers actually accept is the intersection of that
document with competition practice, and the two differ in ways §2 records. There is no
versioned successor: the SAT Competition rules pages are the operative normative source,
and each year's pages are the citable artefact.

The same 1993 document also defines a **non-CNF `p sat` format** with `*` for conjunction,
`+` for disjunction, `-` for negation and parentheses for grouping — arbitrary propositional
formulas, not clauses. It is essentially unimplemented and unused, but §3 records it
because it maps onto HIR more directly than CNF does.

### Reference implementations

CaDiCaL and Kissat (Armin Biere et al.) are the reference-quality open-source solvers and
the usual differential-testing oracles. **Exact current version numbers, repository URLs
and licences were not re-confirmed in this pass** — pin them before differential testing
starts, per the rule `docs/languages-scoping.md` §1.2 applies to QDIMACS's solver choice.

### Corpus

SAT Competition benchmark archives, one per edition, reachable from each year's downloads
page under <https://satcompetition.github.io/>. The Global Benchmark Database
(<https://benchmark-database.de/>, GBD, Iser & Sinz) aggregates instances across editions
with metadata and is the more convenient bulk source.

**Exact instance counts, archive sizes and licence terms: not found** in this pass and
must be settled before any translated instance is republished — the same open item
`docs/languages-scoping.md` §1.2 and §1.7 record for QBFLIB and TPTP. What *is* settled is
that competition benchmarks are publicly downloadable and that instances are distributed
compressed (`.cnf.xz` in recent editions).

---

## 2. Semantics — what a file means

### 2.1 The file

```
c a comment
p cnf <VARIABLES> <CLAUSES>
1 -3 5 0
-1 2 0
```

- **Comment lines** begin with a lower-case `c`. The 1993 document places them in the
  preamble; in practice solvers accept them anywhere.
- **The problem line** is `p cnf VARIABLES CLAUSES`. `VARIABLES` is the largest variable
  index; `CLAUSES` is the clause count.
- **A clause** is "a sequence of numbers, each separated by either a space, a tab, or a
  newline character", terminated by `0`. The document is explicit that this is deliberate:
  "Unlike many formats that represent the end of a clause by a new-line character, this
  format allows clauses to be on multiple lines." The converse also holds — several
  clauses may share a line. **A line is not a clause**, and a reader that assumes it is
  will be wrong on real instances.
- **A literal** is `i` for the positive literal of variable `i` and `-i` for its negation.
  Variables are numbered from 1.

### 2.2 What a solution is

An assignment of `{true, false}` to variables `1 … VARIABLES` satisfying every clause. A
clause is satisfied when at least one of its literals is true. The file's meaning is the
conjunction of its clauses; the answer is SAT (with a model) or UNSAT.

There is **no objective**. `Hir::ConstraintModel::objectives` stays empty and
`Fidelity::preserves_optimum` is vacuously true — "not applicable" rather than "verified
preserved", the same reading `docs/superpowers/specs/2026-08-10-languages-design.md` §4.1.1
prescribes for SyGuS.

### 2.3 Numeric semantics

There are none. Every number in the file is a variable index or the terminator `0`; there
are no coefficients, no weights, no arithmetic. Indices are bounded in practice by what a
solver's `int` holds, and competition instances stay well inside 32 bits.

This is precisely why DIMACS is the cheapest of the twenty-two, and why it is the one
format in this batch immune to the literal-domain problem that §4 of `lp.md`, `mps.md`,
`wcnf.md` and `opb-wbo.md` all run into.

### 2.4 Points the 1993 document leaves open, and what practice does

These are the whole of the format's ambiguity, and a frontend must take a position on each:

| Question | 1993 document | Practice |
|---|---|---|
| Must `CLAUSES` match the number of clauses present? | implied | Solvers vary: some trust the header and stop early, some read to EOF, some abort. Competition instances are well-formed, so the divergence surfaces only on hand-made files. |
| May a variable index exceed `VARIABLES`? | implied not | Usually an error. |
| Do variables in `1 … VARIABLES` that occur in no clause exist? | not stated | They are free variables of the model. Irrelevant to satisfiability; relevant to model counting and to comparing `v` lines in differential testing. |
| Is the empty clause (a bare `0`) legal? | not stated | Accepted by most readers and means `false`, making the instance trivially UNSAT. |
| Duplicate or complementary literals within a clause? | not stated | Legal. A clause containing both `i` and `-i` is a tautology. |
| Is trailing content after the last `0` legal? | not stated | Usually ignored. |

### 2.5 Output, for differential testing

`s SATISFIABLE` / `s UNSATISFIABLE` / `s UNKNOWN`, plus `v` lines listing a full literal
assignment terminated by `0` when satisfiable. Recent competitions additionally require a
DRAT (or LRAT) refutation proof in the main track. **The exact current output and proof
requirements were not re-confirmed against the 2025/2026 rules pages in this pass.**

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New HIR surface required | Fidelity | Notes |
|---|---|---|---|---|
| `c …` comment line | dropped | none | `exact()` | |
| `p cnf V C` problem line | not represented; `V` drives declaration, `C` is validated | none | `exact()` | See §4.2 for the mismatch policy. |
| variable `i` | `VarDecl{name = "x" + i, Sort::boolean()}` | none | `exact()` | Lowered by `hir_to_parser.cpp:131` to `Parser::mkVarBool`. `lower_bound`/`upper_bound` left null. |
| variable declared by the header but occurring in no clause | a `VarDecl` all the same | none | `exact()` | Keeps the model's vocabulary equal to the file's. Omitting it would also be satisfiability-preserving but would change the `v` line, breaking model-level differential comparison. |
| positive literal `i` | `mkIdent("x" + i, Sort::boolean())` | none | `exact()` | |
| negative literal `-i` | `mkOp(Op::NOT, {mkIdent(…)})` | none | `exact()` | |
| clause `l₁ … l_k 0`, `k ≥ 2` | `Constraint{formula = mkOp(Op::OR, {l₁, …, l_k}), soft = false}` | none | `exact()` | `mkOp` is n-ary; `hir_to_parser.cpp:83` forwards it to `Parser::mkOr(args)` which is also n-ary. |
| unit clause `l 0` | `Constraint{formula = l}` — the literal directly, no `OR` wrapper | none | `exact()` | `mkOp(OR, {l})` is legal (arity 1 ≥ 1) but pointless; the builders in the engine would simplify it away anyway (`CLAUDE.md` invariant 2). |
| **empty clause `0`** | `Constraint{formula = mkBool(false)}` | none | `exact()` | **Not** `mkOp(OR, {})` — see §4.1. |
| tautological clause (`i` and `-i` both present) | built as-is | none | `exact()` | The engine's builders simplify before they build (`CLAUDE.md` invariant 2), so this may arrive as `true`. Correct either way; do not assert on the shape. |
| duplicate literals in a clause | built as-is | none | `exact()` | Same note. |
| whole file | `ConstraintModel{decls, constraints, objectives = {}}` | none | `exact()` | Implicit conjunction of the constraints, which is exactly what `HirToParser::lower` produces by asserting each in turn (`hir_to_parser.cpp:157-183`). |
| compressed input (`.cnf.xz`, `.gz`, `.bz2`) | decompressed before parsing | none | `exact()` | Failure is `E_IO`. Not a language concern, but competition archives are compressed, so a frontend that cannot read them cannot see the corpus. |
| **non-CNF `p sat` format** (`*`, `+`, `-`, parentheses) | `Op::AND` / `Op::OR` / `Op::NOT` directly | none | `exact()` | Maps *better* than CNF does — no clause structure to flatten. Unused in practice; implement only if a corpus appears. |
| `c t <track>` / `c p weight` / `c p show` (Model Counting Competition extension) | read and recorded — the weights and the `c p show` projection scope as an `Uir::EncodingChoice` (`strategy = "counting-weights"` / `"counting-projection"`); `c t` is cross-checked against which of those are present | none | `exact()` | `docs/languages-scoping.md` §6.3 records MCC as a *conditional extension of this frontend*, not a language: the headers are read rather than dropped, an unrecognised `c p <directive>` is refused BY NAME (`E_UNSUPPORTED_CONSTRUCT`), and a malformed weight is `E_PARSE`. The lift retains `exact()` on feasibility and objective axes, with model counting unassessed. `Fidelity::count_status` (`include/somtparser/translation/fidelity.h:75`) records that separate assessment; reading a weight or projection header does not establish preservation of its weighted or projected count. |

---

## 4. Semantic gaps and encoding choices

There are none of substance. Every construct in §3 maps exactly, with one construction
edge case, one policy decision, one non-decision, and one engineering risk.

### 4.1 The empty clause is a construction trap, not a semantic gap

`mkOp` opens with

```cpp
// src/hir/hir.cpp
condAssert(!args.empty(), "mkOp: no arguments");
```

and `condAssert` throws `std::runtime_error` and survives `-DNDEBUG`
(`CLAUDE.md` invariant 4). So `mkOp(Op::OR, {})` — the literal reading of "an empty
disjunction" — **throws** rather than producing `false`.

- **Correct mapping**: `mkBool(false)`. Semantically identical, `Fidelity::exact()`, O(1).
- **Failure mode if missed**: `Language::parse()` is contractually required to catch every
  exception and turn it into a diagnostic (`include/somtparser/translation/language.h:111-113`, and
  the design spec §9). An uncaught `condAssert` on a legal input would therefore be a
  frontend bug reported as `E_INTERNAL`, i.e. filed under the wrong bucket of the
  evaluation's failure-cause breakdown — which `include/somtparser/translation/diagnostic.h:17-19`
  is explicitly designed to keep meaningful. Worth an `instances/ok/` fixture.

### 4.2 Header/content mismatch: a diagnostic policy, not an encoding

When `CLAUSES` disagrees with the number of clauses actually present, or a literal index
exceeds `VARIABLES`, there is no encoding question — the file is simply inconsistent.

| Policy | Consequence |
|---|---|
| Trust the header, stop after `CLAUSES` clauses | Silently drops constraints. The translated problem is *weaker*: `sound = false`, `complete = true`. **Reject this**: it produces a wrong answer reported as success. |
| Trust the content, warn on mismatch | `exact()`. The recorded warning keeps the discrepancy visible in `TranslationReport::warnings()`. **Recommended.** |
| Refuse with `E_PARSE` | Also defensible; costs corpus coverage on sloppy but well-understood files. Choose it under `ParseOptions::strict`. |

The asymmetry matters: an over-large `VARIABLES` is harmless (extra free variables, §3),
while an over-small `CLAUSES` is not.

### 4.3 The non-decision: CNF stays CNF

A translation to SMT has no reason to convert, restructure or re-encode clauses. The
project's existing CNF machinery (`src/frontend/conv_parser.cpp`) converts *towards* CNF;
here the input is already there. There is no Tseitin step, no reification, no auxiliary
variable, and therefore no encoding choice to record in `TranslationReport::choices()`.
DIMACS is the only format in Plan 2 for which that is true.

### 4.4 Memory footprint — an engineering risk, not a fidelity one

Recorded here because it is the one way a DIMACS frontend can fail in practice, and
because it is invisible from the fidelity lattice.

`Hir::Expr` (`include/somtparser/hir/hir.h`) carries a `std::string name`, a
`std::vector<ExprPtr> args` and a `SourceLoc` (itself holding a `std::string file`).
Allocated through `make_shared`, one node costs on the order of 140 bytes before its
`args` heap buffer. Competition instances routinely reach millions of clauses and tens of
millions of literals.

A naive frontend that allocates a fresh `Expr` per literal occurrence costs, for an
instance of `m` clauses of average length `k` with a fraction `p` negative,
approximately `m · (1 + k·p) · 140 + m · 8k` bytes of `Expr` and `args` storage. At
`m = 5×10⁶`, `k = 4`, `p = 0.5` that is roughly **2.7 GB** — enough to make a
bulk-translation run fail on ordinary hardware for reasons unrelated to the translation's
correctness.

Two mitigations, both cheap and neither affecting fidelity:

- **Intern literal nodes.** There are exactly `2·VARIABLES` distinct literals in the whole
  file; build each `mkIdent` and each `mkOp(NOT, {ident})` once and share the `ExprPtr`.
  This is the same discipline the mainline engine already enforces by hash-consing
  (`CLAUDE.md` invariant 1). It reduces the estimate above to roughly **0.9 GB**, since
  only the per-clause `OR` node and its `args` buffer remain per clause.
- **Do not populate `SourceLoc::file` per node** for a format this large, or make it an
  interned index. 32 bytes of `std::string` per node is a significant fraction of the
  total for a format with no meaningful per-node source positions to report.


### 4.5 Compact clause storage

Use `options={"packed": "1"}` with `somtparser.translate`
to retain signed literals, clause offsets and one source line per clause in
`PackedBoolClauseBatch`. A `BoolVarRange` retains the complete header vocabulary,
including unused variables. All clauses remain hard; an empty clause emits
`(assert false)`. Files are read as streams in both storage modes.

The default `packed=0` keeps the materialized Parser API. A packed translation
has `uses_packed_smt_stream=True` and `has_parser=False`; use `write_smt2(path)`
for large outputs. Multiline clauses, several clauses per line, counting metadata
and the strict/non-strict header mismatch policy are preserved.

`tools/semantic_checks/cnf_stream_equivalence.py` verifies every source clause
against the complete packed SMT output, including signs and unused variables.
Its certificate concerns the Boolean relation; it does not establish weighted or
projected counting semantics. Unlike the non-strict frontend, the checker requires
consistent header counts. Compilation, solver parsing and solving have separate
outcomes and resource limits in experiment records.

---

## 4.6 What building it settled

**The first obligation is one third of a three-way disagreement**, and that is only visible
with all three frontends in tree:

| Format | What the file's *vocabulary* is | A variable it does not mention |
|---|---|---|
| **DIMACS** | the **header**: `p cnf V C` declares 1..V | still a `VarDecl` — unconstrained, not absent |
| **QDIMACS** | the **prefix** | still binds, and still fixes the alternation depth |
| **QCIR** | the **gates** | free by default |

And the *converse* — a variable the vocabulary does not cover — splits the same three ways: a
warning here (the content declares it anyway), a **refusal** in QDIMACS (`qdimacs.md` §4.5),
and free-by-default in QCIR (`qcir.md` §4.1). `test/languages/test_sat_cross_format.cpp`
asserts the three apart, because each frontend looks right alone and would still look right
with either of the others' rules.

One consequence worth stating: **`num_vars` is not comparable across these formats.** A
DIMACS instance with three variables reports three; the QDIMACS instance that binds three
reports **zero**, because they are bound rather than free. The statistic is honest in each
case and the experiment must not put them in one column.

---

## 5. New HIR surface this format forces

**None.** DIMACS CNF is fully expressible in `Hir` as it stands:
`SortKind::BOOL`, `ExprKind::LIT_BOOL` and `IDENT`, and `Op::OR`/`Op::NOT`. It needs no
literal beyond `mkBool`, no objective, no soft constraint, no new pass, and it exercises no
part of `omt_emitter`.

This is the sense in which `docs/languages-scoping.md` §3.1's cluster B is a real category
— and DIMACS is the only one of its five members for which the claim needs no footnote.
The two adjacent formats are worth naming for contrast:

| Neighbour | What it adds beyond DIMACS | Where documented |
|---|---|---|
| WCNF | per-clause weights, which meet `Constraint::weight`'s `double` and `HirToParser`'s refusal to lower soft constraints | `wcnf.md` §4 |
| QDIMACS | a quantifier prefix — cluster C, a genuine new `ExprKind` | `docs/languages-scoping.md` §1.2, §3.1 |

The one nearby item that *is* worth requesting is not a HIR feature at all: a shared
literal-interning helper for the line-oriented formats (§4.4), reusable by WCNF, QDIMACS
and the propositional encoding path of OPB.

---

## 6. Fidelity summary

**Exact (`Fidelity::exact()`) — the entire format.**

Every construct in §3 has an exact mapping: comments, the problem line, variables,
literals, clauses of any arity, the empty clause, unit clauses, tautologies, duplicate
literals, and unused variables. There is no fragment of DIMACS CNF that is inherently
lossy against an SMT target, because propositional logic is a subset of every logic the
engine supports.

**Inherently lossy: nothing.**

**Ways to make it lossy by mistake** (all avoidable, all listed so a reviewer can check
they were avoided):

- Trusting an under-counting `p` line and dropping clauses — `sound = false` (§4.2).
- Dropping unused variables when the experiment compares models rather than verdicts —
  not a fidelity loss for satisfiability, but a silent change of vocabulary (§3).
- Mapping the empty clause through `mkOp(OR, {})` — throws rather than losing fidelity,
  but is misfiled as `E_INTERNAL` (§4.1).

**Out of scope**: *running* a counter or enumerator over a DIMACS instance from this
frontend. The MCC headers (`c t <track>`, `c p weight`, `c p show`) are read and recorded
rather than dropped — see the §3 row above — but asking the counting question itself is
the Python API's job (`Formula.count()`), per `docs/languages-scoping.md` §6.3; no
counting is performed here.

---

## 7. References

**Format specification**

1. *Satisfiability: Suggested Format*, DIMACS Second Implementation Challenge, last
   revision 1993-05-08.
   <http://archive.dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.tex>

**Competition and corpus**

2. SAT Competition 2025. <https://satcompetition.github.io/2025/> (Main and Parallel
   tracks; results announced 2025-08-15; run on the SoSy-Lab BenchCloud for the first
   time). Per-edition rules, output and downloads pages hang off the same host.
3. SAT Competition portal, all editions. <https://satcompetition.github.io/>
4. Global Benchmark Database (GBD), M. Iser and C. Sinz — cross-edition instance and
   metadata aggregation. <https://benchmark-database.de/>
5. Instance counts, archive sizes and licence terms: **not found** in this pass; an open
   item on the same footing as QBFLIB's and TPTP's in `docs/languages-scoping.md` §1.2
   and §1.7.

**This project**

6. `docs/languages-scoping.md` §3.1 (cluster B), §3.2 (cost 0.2×), §4 (Plan 2), §6.3 (the
   Model Counting Competition as a conditional extension of *this* frontend rather than a
   23rd language).
7. `docs/superpowers/specs/2026-08-10-languages-design.md` §4.1 (the `Fidelity` lattice),
   §4.7 (HIR).
8. `include/somtparser/hir/hir.h`, `src/hir/hir.cpp`, `src/lowering/hir_to_parser.cpp`,
   `include/somtparser/translation/diagnostic.h`, `include/somtparser/translation/language.h`.
