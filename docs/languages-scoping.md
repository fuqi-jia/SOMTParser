# Language scoping: verification, cost, and implementation order

**Date**: 2026-08-11
**Task**: 15 (`.superpowers/sdd/2026-08-10-uir-core-skeleton/task-15-brief.md`)
**Status**: this document is the input Plans 2–5 consume. It writes no product
code; it fixes which of the candidate languages actually ship, in what order,
and why. §1–§5 scoped the 20-language list; §6 audits that list against the
competitions of the field and raises it to 22.

**How to read this document**: §1 answers, per newly-added language, the four
questions the brief requires (spec, corpus, reference implementation,
SMT-LIB basis) and ends with a keep/drop verdict for each. §2 points at the
`Fidelity` resolution now written into the design spec's §4.1.1 (SyGuS-IF and
positive-conjecture TPTP inputs are not satisfiability problems). §3 estimates implementation cost for
all 22 languages (20 at the time of writing, plus §6's two) against
the MiniZinc minimal frontend (Task 12) as
the baseline unit, and flags every language that needs a new HIR feature
separately, since that is core work rather than a parser. MiniZinc and the
SMT-LIB2 baseline are costed alongside the rest because both still have work
left — finishing the frontend and building `SmtToHir` respectively. §4 batches
those 22 into Plans 2–5. §5 points at the collision recheck now written into
`docs/related-work.md` §7.1. §6 was added after the rest, on user request: it
audits the language list against the field's competitions, states the second
filter that principle needs, and adds two languages — its §6.4 lists every
edit it made to §3 and §4, so those sections stay authoritative.

---

## 1. Per-language verification (Step 1)

Scope: the seven languages `§2.1` of the design spec added in round 3
(`docs/related-work-round3-niche-dsls.md`) — Essence′, QDIMACS, VMT-LIB, MoXI,
Boogie, SyGuS-IF, TPTP. The other thirteen (MiniZinc, FlatZinc, XCSP3, LP,
MPS, OPB/WBO, DIMACS CNF, WCNF, BTOR2, AIGER, CryptoLine, CHC-COMP, SMT-LIB2)
were already in the list before round 3 and are not re-litigated here; their
corpus sources appear in §4's table for batching purposes only, sourced from
their own flagship competitions.

For each language: stable spec URL + version, public benchmark corpus
(location / rough size / licence), reference implementation, and whether the
syntax sits on SMT-LIB. Every claim below carries its source. Where a fork
could not find something, it says "not found" rather than guessing, per the
brief's instruction.

### 1.1 Essence′ (`.eprime`)

| Question | Answer |
|---|---|
| Spec | No standalone versioned grammar document exists. The formal EssencePrime grammar lives inside the **Savile Row Manual**, arXiv:2201.03472 (Nightingale et al.) — the same document already cited in `docs/related-work.md` §2.1 for the SMT backend. CSPLib's language page (`https://www.csplib.org/Languages/EssencePrime/`) describes it but carries no independent version number; the grammar's versioning is inherited from Savile Row's own release versioning. |
| Corpus | **Weak.** No competition-scale `.eprime` corpus exists. `EssenceCatalog` (`github.com/conjure-cp/EssenceCatalog`, CC-BY-4.0) holds **Essence** models (the source language one level above Essence′), not Essence′ itself; `.eprime` files are *generated* from it via Conjure in a companion runs repository, not hand-authored or independently curated, and their count is unspecified. Savile Row's own repository ships example `.eprime` files for documentation purposes, not a benchmark set. |
| Reference implementation | **Yes.** Savile Row itself: standalone jar, `https://savilerow.cs.st-andrews.ac.uk/releases.html` (v1.11.0), source at `https://github.com/savile-row/savile-row`. Runs Essence′ → Minion/FlatZinc/SMT and reports SAT/UNSAT/solutions directly, so differential testing against it is feasible. |
| SMT-LIB basis | **No.** Essence′ is a distinct CP modelling syntax (matrix comprehensions, `find`/`such that` blocks) unrelated to the SMT-LIB grammar — confirmed against the actual grammar, not assumed. |
| **Verdict** | **Keep, but the corpus claim must be stated honestly.** Spec and reference implementation are solid — this is also the language that lets the project make the most direct apples-to-apples comparison against Savile Row's own SR-SMT results (`docs/related-work.md` §2.1, the highest-collision-risk neighbour). The "public benchmark corpus" is not a QBFEVAL-style curated archive; it is Conjure-generated `.eprime` output from Essence models. Differential testing is still possible (Savile Row can run the same `.eprime` file we translate), just not against an independently-curated `.eprime`-native competition set. This must be stated plainly in the language's own README when Essence′ is implemented, not glossed over as "has a corpus" on par with, say, XCSP3 or DIMACS. |

### 1.2 QDIMACS (`.qdimacs`)

| Question | Answer |
|---|---|
| Spec | **QDIMACS Standard v1.1**, dated 2005-12-21, `https://www.qbflib.org/qdimacs.html` — stable and versioned, unambiguous. |
| Corpus | QBFLIB, `https://www.qbflib.org/benchmarks_start_page.php` — instances downloadable directly in QDIMACS/QCIR/DQDIMACS format. The page states no explicit licence (contact-only); exact current instance count was not independently re-confirmed. QBFEVAL competition history runs at least through QBFEVAL'23/QBF Gallery 2023 (`https://qbf23.pages.sai.jku.at/gallery/`); a 2024+ edition's corpus size was **not confirmed** — flagged as a follow-up rather than assumed. |
| Reference implementation | QBF solvers (DepQBF, CAQE, etc.) are referenced by QBFLIB's own tooling pages; a specific solver's current maintenance status was **not independently verified** in this pass — pick one concrete solver (recommend DepQBF, still commonly used as the QBFEVAL reference solver) before implementation starts, and confirm it builds. |
| SMT-LIB basis | **No.** The QDIMACS spec text itself says the format is "built on top of the DIMACS standard ... backward compatible with DIMACS" — it is a DIMACS-family line format (`p cnf`-style header, quantifier prefix lines `a`/`e`), not SMT-LIB syntax. |
| **Verdict** | **Keep.** Spec is unambiguous and versioned; QBFLIB provides a real, directly downloadable corpus; the outstanding items (exact licence, exact current-year instance count, final solver pick) are narrow and don't block starting the frontend — they need to be closed before the corpus is used for reported numbers, not before implementation begins. Note for Step 3/4: despite the trivial DIMACS-family grammar, QDIMACS needs a genuine new HIR feature (quantifiers) — see §3. |

### 1.3 VMT-LIB (`.vmt`)

| Question | Answer |
|---|---|
| Specification | *VMT-LIB Format Specification* v0.1 (`es-static.fbk.eu/people/griggio/papers/vmtlib.pdf`) plus *The VMT-LIB Language and Tools*, CEUR Vol-3185 / arXiv:2109.12821. Portal: `vmt-lib.fbk.eu`. An extension of SMT-LIBv2 that encodes a symbolic transition system through **term annotations** (`:next`, and property annotations) rather than new commands. |
| Corpus | ⚠️ **No downloadable curated archive confirmed.** The VMT-LIB initiative states as its goal a collection of model-checking benchmarks for **infinite-state** transition systems, but this pass did not locate a versioned, directly downloadable release the way QBFLIB provides one. Instances exist scattered across the publications that use the format. **Plan for generating a corpus** — e.g. from Lustre/nuXmv sources — rather than assuming download, exactly as for MoXI. |
| Licence | ⚠️ Not established. The format paper is CC BY 4.0; that says nothing about instance licensing. Must be closed before republishing translations. |
| Reference implementation | **nuXmv** (full VMT-LIB support, SMT-based infinite-state verification via MathSAT5); also **Euforia** and **AVR**. **pyVMT** (`github.com/pyvmt/pyvmt`) extends pySMT and can construct and check both finite and infinite-state systems — the most convenient differential-testing harness of the three. |
| Built on SMT-LIB? | **Yes**, and unusually cheaply: it adds no new commands, only annotations, so the existing S-expression and term parser carries almost all of it. |
| **Verdict** | **Keep.** The cheapest of the four transition-system languages to parse, and the only one that brings **infinite-state** models — genuinely complementary to BTOR2's bit-vector finite-state ones rather than overlapping. The corpus must be generated, not downloaded; treat that as scheduled work in Plan 4, not an afterthought. |

### 1.4 MoXI (`.moxi`)

| Question | Answer |
|---|---|
| Spec | No standalone grammar document. The spec lives in two papers: the CAV 2024 tool paper, and **SPIN 2024**, "MoXI: An Intermediate Language for Symbolic Model Checking" (DOI `10.1007/978-3-031-66149-5_2`, PDF `research.temporallogic.org/papers/SPIN2024.pdf`) — the latter is the actual language/semantics paper, distinct from the tool-suite paper. The toolchain repo `github.com/ModelChecker/moxi-mc-flow` (GPL-3.0) ships a reference lexer/parser (`src/parse_moxi.py`, sly lex/yacc) that functions as a de facto formal grammar. |
| Corpus | Small. `moxi-mc-flow/test/moxi/` has **55 hand-written `.moxi` files** (QF_BV/QF_ABV, GPL-3.0); MoXIchecker's own repo ships **21 examples** (Apache-2.0). Native-`.moxi` total across both ≈ 76 files — enough for parser conformance, **not** a standalone benchmark corpus. `moxi-mc-flow/benchmarks/beem/` has 960 `.smv` files (the BEEM suite) that need conversion via `translate.py`; a `.moxi` corpus at any real scale has to be self-generated this way, not assumed ready-made. |
| Reference implementation | **MoXIchecker**, `gitlab.com/sosy-lab/software/moxichecker`, Apache-2.0, open source with a Dockerfile — standalone runnable, produces BMC/k-induction/IC3-PDR verdicts (via PySMT + Z3/MathSAT) for QF_BV/ABV/LIA/NIA/LRA/NRA. Usable for differential testing. **Citation correction**: `docs/related-work.md` and `docs/related-work-round2.md` both previously cited this tool as "TACAS 2025" — cross-checked against dblp, it is actually **VSTTE 2024** (Springer LNCS, DOI `10.1007/978-3-031-86695-1_1`, published 2025-05; TACAS 2025 Part I's table of contents has no MoXI paper). Both files were corrected during this task. |
| SMT-LIB basis | **Yes**, confirmed directly from `parse_moxi.py`'s token set: SMT-LIB2's lexical grammar verbatim, plus a handful of new top-level commands (`define-system`, `check-system`, `declare-enum-sort`), new attribute keywords (`:input :output :local :init :trans :inv :subsys ...`), and one lexical wrinkle (`SYMBOL` allows a trailing `'` for primed next-state variables, non-standard but minor). A thin SMT-LIB2 superset, not a syntactic divergence. |
| **Verdict** | **Keep.** The design's own `TransitionSystem` shape is modelled on MoXI's `define-system` (already established in `docs/related-work-round2.md` §2); this pass confirms the toolchain, reference checker, and SMT-LIB basis are all real and runnable, not just described in a paper. The one caveat to carry forward: a usable-scale benchmark corpus must be generated from BEEM/SMV via `translate.py`, not assumed to exist natively. |

### 1.5 Boogie (`.bpl`)

| Question | Answer |
|---|---|
| Spec | "This is Boogie 2" (K.R.M. Leino, manuscript KRML 178, 2008-06-24) remains the de facto authoritative reference. `boogie-org/boogie-docs`'s `LangRef.rst` (`https://boogie-docs.readthedocs.io/en/latest/LangRef.html`) explicitly self-describes as "very out-of-date" and does not supersede KRML 178; gaps (e.g. the floating-point extension) must be patched from the current wiki/source. No newer formal spec exists. |
| Corpus | `boogie-org/boogie`'s own regression suite: ~760 `.bpl` files (GitHub code search, `extension:bpl repo:boogie-org/boogie`), MIT licensed. A much larger real-world corpus is reachable via **Dafny** (`dafny-lang/dafny`, ~2,244 `.dfy` files), which compiles to Boogie (`dafny -print:a.bpl HelloWorld.dfy`) — thousands of realistic `.bpl` files on demand, not hand-authored. |
| Reference implementation | `boogie-org/boogie`, **MIT, actively maintained** (last push 2026-08-06, latest release v3.5.7, 2026-07-26, 597 stars). Installable via `dotnet tool install --global boogie`; runs standalone on `.bpl`, invokes Z3 by default, produces a verify/error verdict directly usable for differential testing. |
| SMT-LIB basis | **No.** Imperative C-like grammar (`procedure`, `requires`/`ensures`/`modifies`, `assert`/`assume`/`havoc`, `if`/`while`/`goto`) — needs a parser from scratch, and (unlike every other language in this table) a real VC-generation pipeline: CFG cutting at loops using supplied invariants, passification (SSA-style assume-conversion), then weakest-precondition computation. This is not "a harder parser," it's an additional compiler stage with no analogue elsewhere in the 19. |
| **Verdict** | **Keep, but flag prominently as not low-cost.** The design spec's §2.1 summary paragraph names VMT-LIB/MoXI/SyGuS-IF/QDIMACS as the low-cost additions and is silent on Boogie — confirmed that silence is intentional, not an oversight. No source was found quantifying what fraction of real Dafny-generated `.bpl` is loop-free (would need VCGen only in its simplest form); recommend scoping the frontend to straight-line procedures plus loops with user-supplied invariants (no general invariant inference), and running a quick census of Dafny's own test-suite `.bpl` output for loop-free vs. looping procedures before Plan 5 starts, to size the risk instead of guessing at it. |

### 1.6 SyGuS-IF (`.sl`)

| Question | Answer |
|---|---|
| Spec | `sygus-org.github.io/language/`, confirmed live. Current version **SyGuS-IF 2.1** (extended 2021: oracle specification, weighted SyGuS, a theory of tables, a CHC logic), PDF at `sygus-org.github.io/assets/pdf/SyGuS-IF_2.1.pdf`, mirrored as arXiv:2312.06001. §2.9's `Cmd` grammar formally defines `synth-fun`/`declare-var`/`constraint`/`check-synth`. |
| Corpus | `github.com/SyGuS-Org/benchmarks` (43 stars, 7 forks), confirmed live. `comp/` holds official competition sets only for **2017–2019**; `lib/` holds 5 current tracks (`CLIA_Track`, `General_Track`, `Inv_Track`, `PBE_BV_Track`, `PBE_SLIA_Track`). **No LICENSE file** (GitHub API reports `license: null`). Last merged PR: 2023-03-30 — sporadic maintenance, not competition-driven. |
| Competition status | The official "Past Competitions" page lists only 2014–2019; no evidence of a 2020–2026 edition. **SyGuS-Comp has been dormant for roughly seven years.** (Note: the legacy `sygus.org` domain has been squatted; the canonical live site is `sygus-org.github.io`.) |
| Reference implementation | **cvc5**, latest release **cvc5-1.3.4** (2026-05-07), actively maintained, with a documented SyGuS engine (`synth-fun`/`checkSynth`, CLI `check-synth`) producing a solution or "no solution" — usable for differential testing. Caveat: the 2.1-specific `declare-weight`/weighted-SyGuS extension is reportedly **not yet supported** in cvc5 (per a cvc5 GitHub discussion); core 2.1 syntax works, full 2.1 feature coverage doesn't. |
| SMT-LIB basis | **Yes**, confirmed from the spec text itself (§1: "borrows … the SMT-LIB standard (version 2.6)"). |
| **Verdict** | **Keep.** Spec is live and versioned, the syntax is formally SMT-LIB-based (cheap parser), and cvc5 is a real, current differential-testing target. The two risks to carry forward honestly: the competition itself is dormant (no fresh benchmark pressure or community momentum since 2019) and the benchmark repo has no stated licence — treat the corpus as reference-only until licensing is clarified with the maintainers. |

### 1.7 TPTP (`.p`, TFF subset)

| Question | Answer |
|---|---|
| Specification | `tptp.org` — TPTP Technical Report / Problem Library Manual, versioned. Logic hierarchy CNF / FOF / TFF (mono + poly, incl. TXF) / THF / DHF; interpreted arithmetic types and symbols exist in the typed forms, which is what makes the **TFF subset** the relevant target. |
| Corpus | TPTP **v9.0.0**: 15888 abstract problems yielding **25775 ATP problems**, downloadable from `tptp.org`. Largest corpus of any language on this list by an order of magnitude. |
| Licence | ⚠️ **Not established in this pass.** The library is publicly distributed and universally used in CASC, but the exact redistribution terms were not confirmed. Must be settled before any TPTP-derived instance is republished as part of the standardised OMT/SMT benchmark deliverable (§2.2 item 7) — reading it for experiments is a weaker requirement than redistributing translations of it. |
| Reference implementation | **E** (3.2.5) and **Vampire** (4.10) both consume TPTP directly and are current; either serves as a differential-testing oracle. CASC has run annually since 1996. |
| Built on SMT-LIB? | **No.** Prolog-like clause syntax, no reuse of the SMT-LIB S-expression parser — this is the cost driver behind the 2.5× estimate in §3.2. |
| **Verdict** | **Keep.** Uniquely large corpus and two live reference provers. Two caveats to carry: the licence question above must be closed before redistribution, and a TPTP input containing a positive `conjecture` is a **validity** problem whose refutation negation happens at parse/lowering time. Axiom-only and `negated_conjecture`-only inputs remain satisfiability problems. |

### 1.8 Verdict summary

All seven survive verification. **None is waved through** — each carries a named
caveat that changes how it must be planned or reported.

| Language | Verdict | The caveat that matters for planning |
|---|---|---|
| Essence′ | Keep | **No curated corpus.** Only Conjure-generated `.eprime`; differential testing against Savile Row still works, but this must be stated plainly in the language README, not presented as corpus parity with XCSP3 or DIMACS. |
| QDIMACS | Keep | Trivial grammar, but needs a **new HIR feature** (quantifiers, cluster C). Cheap parser ≠ cheap language. |
| VMT-LIB | Keep | Corpus must be **generated**, not downloaded. Reuses the SMT-LIB parser almost entirely. |
| MoXI | Keep | Corpus must be **generated** from BEEM/SMV via `translate.py`. Reference checker (MoXIchecker) is real and runnable. |
| Boogie | Keep | **Explicitly not low-cost** — 3.0×+, the heaviest of the twenty-two. Needs a WP/passification VC generator, and that generator *is* the translation. Scope to straight-line plus user-supplied invariants; census Dafny's `.bpl` output before Plan 5 to size the risk rather than guess. |
| SyGuS-IF | Keep | Competition **dormant since 2019**; benchmark repo has **no stated licence**. Treat the corpus as reference-only until clarified. |
| TPTP | Keep | Largest corpus of all twenty-two (25775 problems), two live reference provers — but **licence unconfirmed** for redistribution, and positive-conjecture inputs require the validity mapping described in §2. |

**Two conclusions that change later plans**, both recorded in full below:
- the bit-vector `Sort` scheduling conflict (§4.2) — it cannot stay in a notional
  "Plan 6" because BTOR2, AIGER and CryptoLine need it and all remaining languages
  must land in Plans 2–5;
- SyGuS-IF requires a new `Bound::Kind::GRAMMAR_RESTRICTION` (§2), because a
  grammar is not expressible as any of the existing scalar bounds.

---

## 2. `Fidelity` semantics for non-satisfiability inputs (Step 2)

Written into the design spec directly, `docs/superpowers/specs/2026-08-10-languages-design.md`
§4.1.1, since it changes the spec's own definitions and belongs there rather
than duplicated here. Summary of the conclusion (see the spec for the full
derivation and the exact SyGuS-IF 2.1 terminology it is checked against):

- **No new axis.** `sound`/`complete` are defined in `fidelity.h` in terms of
  "a found solution is real" / "no solution is lost" — wording that already
  generalises past pure satisfiability. Both SyGuS (synthesis) and TPTP
  (validity) reinterpret cleanly under that reading.
- **SyGuS**: `check-synth`'s answer is a function, and the SyGuS-IF 2.1
  standard's own notion of `infeasible` is defined over the *unrestricted*
  existential problem (realizability), not "no solution in this grammar" —
  so `sound`/`complete` carry over to "the synthesized function really
  satisfies the spec" / "no solution is lost by the translation" without
  rewording. The grammar itself is not our approximation (it's the problem
  statement); only a translation-forced *narrowing* of the grammar (because
  HIR can't represent some production) is. That case needs a new
  `Fidelity::Bound::Kind::GRAMMAR_RESTRICTION`, since none of the four
  existing kinds (`BMC_DEPTH`, `BV_WIDTH`, `DOMAIN_CUT`, `HORN_UNROLL`) are
  shaped to record "bounded by a grammar" rather than a scalar.
- **TPTP with a positive `conjecture`**: validity (`axioms ⊨ conjecture`) is the proof-theoretic dual of
  satisfiability (`axioms ∧ ¬conjecture` is unsatisfiable). The frontend
  performs that negation at the HIR-lowering stage, before `Fidelity` ever
  sees the problem, so `Fidelity`'s existing two axes apply unchanged to the
  rewritten satisfiability problem — **no new `Bound::Kind` needed for
  TPTP**. The mapping is: `sound` governs trust in a `CounterSatisfiable`
  verdict (translated SAT), `complete` governs trust in a `Theorem` verdict
  (translated UNSAT) — note this is the *reverse* of the usual intuition
  that `complete` is the "safe, secondary" axis; for TPTP `complete` guards
  the result users actually want (a proof).
- `E_UNSUPPORTED_CONSTRUCT` triggers on constructs with no HIR/SMT-LIB
  counterpart at all (THF higher-order quantification, unsupported TPTP
  include namespaces, SyGuS's non-context-free grammar extensions or `oracle`
  constraints) — kept explicitly separate from `Fidelity`: a formula that
  lands outside a solver's decidable fragment but was translated exactly is
  still `Fidelity::exact()`; that is the solver's limitation, not the
  translation's.

---

## 3. Implementation cost estimate (Step 3)

**Baseline unit = 1.0×**: the MiniZinc minimal frontend (Task 12,
`languages/minizinc/src/mzn_minimal.cpp`, 411 lines). Hand-written lexer +
recursive-descent parser; `var`/`constraint`/`solve` items; range domains;
11 `Hir::Op` values (`AND OR NOT EQ LE LT GE GT ADD SUB MUL`); no arrays,
sets, comprehensions, global constraints, or `.dzn` data files. It touches
zero core HIR surface — `Hir::ConstraintModel` as it stands today
(`decls`/`constraints`/`objectives`, `SortKind{BOOL,INT,REAL}`) was already
sufficient.

**What "new HIR feature" means concretely, checked against the actual code,
not assumed**: `Uir::Hir::Expr` today has four `ExprKind`s
(`LIT_BOOL`, `LIT_INT`, `IDENT`, `OP`) and three sorts (`BOOL`, `INT`,
`REAL`) — no bit-vectors, no quantifiers, no function application, no
uninterpreted sorts, no arrays, no `TransitionSystem` (the
design spec's §4.7 sketch of those is aspirational; the implemented type is
narrower and is called `ConstraintModel`, not `Model` — see
`include/somtparser/hir/hir.h`). Importantly, the **underlying mature
SMT-LIB engine `SOMTParser::Parser`/`DAGNode` that HIR lowers onto already
supports all of these** — bit-vectors (`include/somtparser/core/kind.h`,
`NT_BV_*`), quantifiers (`parser.h:3394 mkForall`, `parser.h:3402 mkExists`),
and uninterpreted function application (`parser.h:810 mkApplyUF`). So a "new
HIR feature" below means extending the small `Uir::Hir` walking-skeleton
layer plus one new `switch` case in `src/lowering/hir_to_parser.cpp`
(171 lines, one case per `ExprKind` today) — not extending the solver-facing
engine, which is a separate, much cheaper problem than it would be starting
from nothing.

### 3.1 Shared new-HIR-feature clusters

| Cluster | New HIR surface | New pass | Languages |
|---|---|---|---|
| A. Global constraints + arrays | array/collection representation + a global-constraint call form + reification | decomposition pass per global (e.g. `alldifferent` → pairwise/bitmask, cf. CP2020 SR-SMT's two encodings) | MiniZinc (finish), FlatZinc, XCSP3, Essence′ |
| B. None (fits `ConstraintModel` today) | — | — | DIMACS CNF only. LP, MPS, OPB/WBO and WCNF were listed here in error (`docs/risks-2026-08-12.md` §3.4, correction applied 2026-09-18): LP/MPS needed the text-backed real literal (`Hir::mkReal(std::string)`), OPB/WBO the text-backed big-integer literal and WCNF the text-backed weight (`Constraint::weight_text`). |
| C. Quantifiers | new `ExprKind::FORALL`/`EXISTS` over a bound `VarDecl` list | **none** — SMT-LIB natively expresses quantifiers, so this is a straight pass-through to the engine's existing `mkForall`/`mkExists`, unlike every other cluster here | QDIMACS, TPTP, SYNTCOMP (§6.3) |
| D. `TransitionSystem` | new struct: `inputs`/`outputs`/`locals`/`init`/`trans`/`invariants`/`properties` (MoXI-shaped, per design spec §4.7) | bounded unrolling (BMC), `Fidelity::underApprox(BMC_DEPTH)` | BTOR2, AIGER, VMT-LIB, MoXI, PDDL (§6.3, adds `PLAN_HORIZON` + a reachability flag on `properties`), SYNTCOMP (§6.3) |
| E. Horn normal form | existing `FunDecl` relations + `FORALL` + `APPLY`; source shape is validated before generic HIR lifting | none for exact SMT embedding; optional Horn unrolling is operational only | CHC-COMP |
| F. Bit-vector `Sort` | widen `SortKind` with `BV`, width-parameterised | (lowering strategy itself is Plan 6's scope; the *sort* is a prerequisite, see §4.2 risk note) | BTOR2, CryptoLine |
| G. Function/predicate application + user sorts | new `ExprKind::APPLY` + function-signature declarations + non-numeric `SortKind` | none required for direct translation (target engine already has `mkApplyUF`) | TPTP, Boogie |
| H. Program → VC generation | not a HIR struct addition — a frontend-level symbolic-execution / weakest-precondition pass, specific to each language's control-flow model | Boogie: full WP over procedures/loops (loop unrolling or trusted invariants); CryptoLine: much smaller straight-line SSA instance of the same pattern | Boogie, CryptoLine |
| I. Synthesis goal | new top-level struct parallel to D/E: function signature + grammar + semantic constraints; `Feature::syntacticRestriction()`; `Bound::Kind::GRAMMAR_RESTRICTION` (§2) | none for direct translation; the interesting cost is architectural (a `check-synth` problem does not fit `decls`/`constraints`/`objectives`) | SyGuS-IF |
| J. None | — | — | SMT-LIB2 (baseline) |

### 3.2 Per-language relative cost

The cluster letters below record the planning-era batching. Per the §3.1
correction (2026-09-18), WCNF, OPB/WBO, LP and MPS are not strictly
cluster-B members: each consumed a small text-backed HIR extension
(literals or `Constraint::weight_text`) rather than fitting the HIR exactly
as it existed. Their cost estimates are unaffected.

| Language | Relative cost | Cluster(s) | Drivers |
|---|--:|---|---|
| DIMACS CNF | **0.2×** | B | Cheapest of all 22: one clause = one `Constraint`, no objective, no types. |
| SMT-LIB2 (baseline) | **0.2×** | J | Already the native format; round-trip self-test only. |
| WCNF | **0.3×** | B | DIMACS + per-clause weight; `Constraint.soft`/`weight` already exist in HIR. |
| OPB/WBO | **0.4×** | B | Linear PB constraints + optional objective/top weight; fits existing `ADD`/`MUL`/comparisons and `Constraint.soft` exactly. |
| LP (CPLEX) | **0.5×** | B | Plain linear objective + constraints + bounds sections; simpler grammar than MiniZinc minimal. |
| MPS | **0.7×** | B | Same semantics as LP but fixed-column lexing + multiple sections (`RANGES`/`BOUNDS`/`RHS`) is lexically fussier; may pair a model file with a separate bounds file (`SourceUnit::data_paths` already supports this). |
| QDIMACS | **0.6×** | C | Grammar is DIMACS-cheap (prefix `a`/`e` lines), but needs the new quantifier `ExprKind` (shared with TPTP) — flagged as a **new-HIR-feature language** despite the trivial parser. |
| VMT-LIB | **0.7×** | D | Literally SMT-LIB2 + `:next` annotations — reuses the existing S-expression/term parser almost entirely. Needs `TransitionSystem` (shared cluster D cost, amortised across 4 languages). **New HIR feature.** |
| MoXI | **0.8×** | D | New top-level command grammar (`define-system`/`check-system`, not standard SMT-LIB2 commands) on top of reusable term/sort parsing; HIR's `TransitionSystem` is modelled directly on it, so the mapping is closest to 1:1 of the whole cluster. **New HIR feature** (shared with VMT-LIB/BTOR2/AIGER). |
| CHC-COMP | **0.8×** | E | SMT-LIB parsing reuse plus strict command/normal-form validation; existing quantified relation HIR gives an exact embedding. |
| MiniZinc (finish) | **1.0×** (baseline) + **~1.5×** more to finish | A | Task 12 already covers the walking-skeleton grammar; finishing means `.dzn` data, arrays, comprehensions, global constraints — cluster A's full cost lands here first. **New HIR feature.** |
| AIGER | **1.0×** | D (+ shares BMC pass) | Extremely regular bit-level format (ASCII or binary AIG); no BV sort needed (pure Boolean) so it is the cheapest language in cluster D. **New HIR feature** (`TransitionSystem`). |
| SyGuS-IF | **1.2×** | I | SMT-LIB 2.6 term/sort parsing reused (`synth-fun`/`declare-var`/`constraint`/`check-synth` are the only new commands); the cost is architectural novelty (a `SynthesisGoal` payload, not an `Expr` extension) rather than grammar. **New HIR feature.** |
| FlatZinc | **1.3×** | A | Shares MiniZinc's global-constraint/array HIR work once cluster A exists; own grammar is simpler than MiniZinc source (fully flattened, static indices) but is its own compile target with its own reification idioms. **New HIR feature** (shared with MiniZinc). |
| BTOR2 | **1.5×** | D + F | Word-level line format is lexically simple, but needs **two** new HIR features: `TransitionSystem` (cluster D, shared) **and** a bit-vector `Sort` (cluster F) — flagged specifically because F is currently scoped to Plan 6, after all four language plans (see §4.2 risk). |
| CryptoLine | **1.5×** | F + H | Needs bit-vector `Sort` (cluster F, shared with BTOR2) plus a VC-generation pass — but a much smaller instance than Boogie's, since CryptoLine programs are straight-line (no branches/loops), so SSA + assert-postcondition is comparatively mechanical. |
| SYNTCOMP (AIGER-EXT safety track) | **1.5×** | C + D | Parser is ~0.2× marginal over AIGER (AIGER plus a controllable-input convention in the symbol table); the cost is the **bounded-realizability encoding** — a safety game is ∃strategy ∀environment, so one quantifier alternation per unrolled step, which lands on cluster C's surface, not on the parser. See §6.3 for why it is kept despite the cost: SYNTCOMP is live where SyGuS-Comp is dormant. |
| PDDL (IPC) | **1.8×** | D | Grammar ~0.7× (Lisp-style S-expressions; two files per instance, domain + problem, which `SourceUnit::data_paths` already supports as MPS does), plus a **grounding pass** — instantiating action schemas over the object universe — of roughly cluster A's decomposition-pass size, plus numeric fluents. Reuses cluster D's `TransitionSystem` and BMC unrolling. **New HIR feature** (cluster D, shared) and a new `Bound::Kind::PLAN_HORIZON` (§6.3). |
| XCSP3 | **2.0×** | A | XML parsing plus dozens of global-constraint schemas (`docs/related-work-round2.md` §3's XCSP3-core catalogue, ~20 constraint families before counting variants); consumes cluster A's decomposition-pass library once it exists from MiniZinc/FlatZinc. **New HIR feature** (shared). |
| Essence′ | **2.0×** | A | Matrix comprehensions and quantified `find`/`such that` blocks are comparable in complexity to MiniZinc's own comprehension support, on top of a distinct concrete syntax; benefits from cluster A's pass library but adds real grammar cost of its own. **New HIR feature** (shared). Corpus is the weak point (§1.1), not the implementation. |
| TPTP (TFF) | **2.5×** | C + G | Fully new lexer/grammar (Prolog-like clause notation, no reuse from SMT-LIB or MiniZinc's C-like grammar) **and** two new HIR features: quantifiers (shared with QDIMACS) and function/predicate application + user sorts (shared with Boogie) — the largest grammar rewrite of the batch layered on top of the largest count of distinct new HIR needs. |
| Boogie | **3.0×+** | G + H | Heaviest single language. Procedures, control flow (`if`/`while`/`goto`), `assert`/`assume`/`havoc`, `requires`/`ensures`, `old()`, maps. Needs function/predicate application (cluster G, shared with TPTP) plus a full weakest-precondition/passive-transformation VC generator — and that VC generation *is* the translation's semantic core, not a separable "parser vs. pass" split the way every other language in this list has. Partially de-risked by benchmarks being tool-generated (Dafny etc. typically emit loop invariants already, see §1.5), but this is still the single largest frontend by a wide margin. |

**Languages needing a new HIR feature, called out per the brief's instruction**
(everything except cluster B and the SMT-LIB2 baseline; per
`docs/risks-2026-08-12.md` §3.4 only DIMACS CNF is genuinely in cluster B —
LP, MPS, OPB/WBO and WCNF also needed new HIR surface, delivered as the
text-backed literals and text-backed weight noted in §3.1):
MiniZinc (finish), FlatZinc, XCSP3, Essence′ (cluster A) · QDIMACS, TPTP,
SYNTCOMP (cluster C) · VMT-LIB, MoXI, BTOR2, AIGER, PDDL, SYNTCOMP
(cluster D) · CHC-COMP (cluster E) · BTOR2, CryptoLine (cluster F, BTOR2
counted once) · TPTP, Boogie (cluster G) · SyGuS-IF (cluster I). Only
**DIMACS CNF** is pure-parser work against the HIR as it exists today.

---

## 4. Batching into Plans 2–5 (Step 4)

Two ordering rules, per the brief: (1) languages sharing a lowering pass land
in the same plan, so that pass is not reworked across several plans; (2)
languages with a public corpus *and* a reference implementation come first,
because the differential-validation framework cannot start without at least
one of each.

**This table supersedes two earlier, informal plan-number mentions** written
before the round-3 language expansion made this scoping pass necessary:
Task 12's MiniZinc `README.md` template said "the full MiniZinc
implementation … lands in Plan 2"; Task 16's rationale said real `int`→BV
"needs a bitvector sort added to HIR, a core change, and belongs to Plan 6's
scope" (`task-16-brief.md` lines 13–14). Neither is wrong on its own terms —
both were written when the language list had 12 entries, not 20 — but Task 15
is the authoritative source for Plan 2–5 assignments going forward, and both
placeholders are revised below, for the reasons given in §4.2.

| Language | Plan | New HIR feature | New pass | Corpus source |
|---|:--:|---|---|---|
| DIMACS CNF | **2** | none | none | SAT Competition archives; CaDiCaL/Kissat as reference |
| WCNF | **2** | none | none | MaxSAT Evaluation archives; EvalMaxSAT/other MaxSAT solvers |
| OPB/WBO | **2** | none | none | PB Competition archives; RoundingSat/Sat4j-class PB solvers |
| LP | **2** | none | none | MIPLIB and vendor LP corpora; Gurobi/CBC/SCIP |
| MPS | **2** | none | none | MIPLIB (native MPS); Gurobi/CBC/SCIP |
| QDIMACS | **2** | quantifier `ExprKind` (cluster C, introduced here at its cheapest — Bool-only, untyped) | none (exact translation) | QBFLIB (§1.2); DepQBF or another maintained QBF solver, pinned before implementation |
| MiniZinc (finish: `.dzn`, arrays, comprehensions, globals) | **3** | cluster A: arrays/collections, global-constraint call form, reification | global-constraint decomposition pass (shared by the whole cluster) | MiniZinc Challenge |
| FlatZinc | **3** | cluster A (shared with MiniZinc) | shared decomposition pass | MiniZinc Challenge `.fzn` output; Chuffed/OR-Tools |
| XCSP3 | **3** | cluster A (shared); adds its own large global-constraint schema catalogue | shared decomposition pass, extended for XCSP3-specific constraint families | XCSP3 Competition archives; competition solvers |
| Essence′ | **3** | cluster A (shared); adds matrix comprehensions | shared decomposition pass | CP2020-SRSMT's bundled `.eprime` models (§1.1 — weak corpus, stated honestly); Savile Row's own native backends (Minion/Gecode/Chuffed) as reference |
| MoXI | **4** | cluster D: `TransitionSystem`/`Property` (this language is the shape's origin) | none new (defines the struct) | Self-generated from BEEM via `moxi-mc-flow`'s `translate.py`, plus the ~76 native example files (§1.4); MoXIchecker |
| VMT-LIB | **4** | cluster D (shared with MoXI) | none new | *pending §1.3* |
| BTOR2 | **4** | cluster D (shared) **and** cluster F: bit-vector `Sort` (pulled forward from the "Plan 6" placeholder — see §4.2) | BMC unrolling pass (`Fidelity::underApprox(BMC_DEPTH)`), shared with AIGER/VMT-LIB/MoXI | HWMCC archives; ABC/BtorMC/AVR |
| AIGER | **4** | cluster D only (reuses BTOR2's BV sort work but doesn't need BV itself — pure single-bit signals) | shared BMC pass | HWMCC archives; ABC |
| PDDL (§6.3) | **4** | cluster D (shared) + `Bound::Kind::PLAN_HORIZON` + a **safety/reachability flag** on `properties`, since a planning goal is the dual of the safety properties the rest of cluster D checks | grounding pass (action schemas × object universe) + the shared BMC unrolling pass | IPC 2023 numeric track (380 tasks / 36 domains) and archived classical-track corpora; competition planners as reference |
| CryptoLine | **4** | cluster F (reuses BTOR2's bit-vector `Sort`) | cluster H: a small, straight-line VC-generation pass (no branches/loops, so SSA + postcondition assertion is mechanical compared to Boogie's) | Not independently sized in this pass — flagged as a follow-up before Plan 4 starts (see §1 note); not compared for performance against CoqCryptoLine, only included as one cross-domain data point per `docs/related-work.md` §6 |
| CHC-COMP | **3** | cluster E validation over existing quantified relation HIR | none required for semantic preservation; solver-native Horn handling is an operational option | CHC-COMP archives; Spacer(Z3)/Eldarica |
| SyGuS-IF | **5** | cluster I: synthesis-goal struct (function signature + grammar + constraints) + `Bound::Kind::GRAMMAR_RESTRICTION` (§2) | none for direct translation | `SyGuS-Org/benchmarks` (§1.6 — licence unstated, competition dormant since 2019); cvc5 |
| SYNTCOMP, AIGER-EXT safety track (§6.3) | **5** | cluster C (quantifier alternation, generalising QDIMACS's Plan 2 introduction) + cluster D (shared with AIGER, Plan 4) | bounded-realizability encoding: one ∃controllable/∀uncontrollable alternation per unrolled step, `Fidelity::underApprox` on the step bound | SYNTCOMP benchmark repository, curated per edition and **live** — the reason this is kept despite the cost, since SyGuS-Comp is not (§1.6) |
| TPTP | **5** | cluster C (typed, general quantifiers — generalises what QDIMACS introduced in Plan 2) **and** cluster G (uninterpreted sorts/functions/predicates) | the validity→satisfiability negation happens at parse/lowering time, not as a `PassManager` pass (§2) | *pending §1.7* |
| Boogie | **5**, sequenced last | cluster G (shared with TPTP) | cluster H: full WP/passification VC generation, scoped to the straight-line-plus-annotated-invariants subset (§1.5) | `boogie-org/boogie` regression suite + Dafny-generated `.bpl`; Boogie itself as reference |
| SMT-LIB2 (baseline, builds `SmtToHir`) | **5**, sequenced first within the plan | none (a lifter, not a new feature) | none | Existing SMT-LIB round-trip test corpus |

### 4.1 Cross-plan sharing, called out because it doesn't fit the simple
"same batch, same pass" rule

- **Quantifier `ExprKind`**: introduced in Plan 2 for QDIMACS (the cheapest
  possible case — untyped, Bool-only), then reused and generalised by TPTP in
  Plan 5 (typed, over arbitrary sorts). A deliberate two-plan split, not
  duplicated work, because cramming TPTP into Plan 2 to keep the feature in
  one plan would force Plan 2's easy, high-corpus batch to also absorb TPTP's
  from-scratch grammar and EUF cost.
- **`SmtToHir`**: does not exist in the tree today (confirmed — no
  `SmtToHir`/`smt_to_hir` symbol anywhere under `include/`/`src/`). The design
  spec (§6.1 rule 3) requires CHC-COMP and the SMT-LIB2 baseline to lift
  through it. VMT-LIB and MoXI (Plan 4) do **not** need to wait for it: both
  need only a small subset of SMT-LIB2 term/sort syntax plus their own
  extensions, and a self-contained lightweight S-expression reader inside
  each language's own module is both cheaper and more consistent with the
  design spec's "each language directory is self-contained" rule (§6.1
  rule 1) than a cross-plan dependency on Plan 5. This should be written down
  explicitly when Plan 4 starts, not left implicit.
- **Bit-vector `Sort`**: introduced in Plan 4 by BTOR2, reused by AIGER
  (nominally — AIGER itself doesn't need it) and CryptoLine in the same plan.
  See §4.2 for why this supersedes the "Plan 6" placeholder.

### 4.2 Risk: the "Plan 6" bit-vector placeholder no longer holds

Task 16's rationale (written before this scoping pass) explicitly deferred
real `int`→bitvector lowering to "Plan 6" specifically *because* it requires
a new HIR sort and is a core change (`task-16-brief.md` lines 13–14; also
visible in `src/translation/profile.cpp`'s `bv32` profile, which today only bounds
`Int` domains and says so in its own comment). That was a reasonable scope
cut for Plan 1, which only needed to prove the fidelity pipeline worked at
all with a lossy pass, not build a real bit-vector theory bridge.

But three of the languages this document is scoping — BTOR2,
AIGER (indirectly, via shared cluster D infrastructure with BTOR2), and
CryptoLine — **cannot be faithfully represented without a real bit-vector
`Sort`**, and the brief requires all of them to land in Plans 2–5. There is
no room left for a separate "Plan 6 first, then the languages that need it."
**Resolution: bit-vector `Sort` moves from the placeholder "Plan 6" into
Plan 4**, where BTOR2 already needs it. This is not extra scope invented by
this document — it is a scheduling conflict that only became visible once
the language count grew from 12 to 20 and Task 15 went looking for exactly
this kind of dependency. Two mitigating factors keep this from being as
large a lift as it sounds: (a) the underlying `SOMTParser::Parser`/`DAGNode`
engine already has full bit-vector support (`core/kind.h`'s `NT_BV_*` node
kinds) — the work is a thin `Uir::Hir` adapter, not a new theory
implementation; (b) Plan 4 was already going to touch `PassTraits`/pass
infrastructure for BMC unrolling, so a second HIR-surface change lands in
the same review cycle rather than a separate one.

---

## 5. Collision recheck (Step 5)

Full record now written into `docs/related-work.md` §7.1. Summary: a live
rescan on 2026-08-11 of **CP 2026, CPAIOR 2026, SAT 2026, CAV 2026, TACAS
2026** accepted-paper lists (all five 2026 editions had already been held and
published proceedings by that date, so this was a check of real listings, not
a forecast) found:

- **No SMT/OMT encoding-selection work.** CP 2026 has one paper in the
  neighbourhood — "SMT-Select: Learning Unified Graph and Language
  Representations for SMT Algorithm Selection" — but on inspection it
  selects which *solver* to run (portfolio selection, the MachSMT family),
  not which *encoding* to translate into. Different research question, no
  collision. The Savile Row/SR-SMT group's own 2025–2026 output
  (Nightingale, Akgün) covers argumentation mining, local search, symmetry
  breaking and algorithm-selection methodology — nothing on SMT encoding
  choice. Their CP 2020 paper's self-declared future-work item ("a portfolio
  of SMT encodings") remains unfilled by its own authors. **C3 stands.**
- **No cross-community frontend competitor.** Nothing spanning more than one
  solver community (CP, MIP, SAT, hardware model checking, program
  verification, synthesis, theorem proving) and translating to SMT/OMT
  appeared at any of the five venues. TACAS 2026 published the full version
  of "Exploring the SMT-LIB Benchmark Library" (the SMT 2025 workshop paper
  already cited in `docs/related-work-round2.md` §8) — it strengthens this
  project's C2 motivation, it is not a competing contribution.

No changes to the collision-risk assessment were needed as a result; the
rescan is recorded as a dated, checked negative rather than an unchecked
assumption, per the brief's explicit instruction that a checked negative is
a valid and useful outcome.

---

## 6. Competition coverage audit (Step 6)

**Origin**: not part of the Task 15 brief. Added on user request, 2026-08-11:

> 我觉得对于这种约束求解或者相关的有比赛，都可以建立前端对应，这样的话就能全面
> 吸收哪些领域的 benchmark 了。你调研下还有没有可以加入的。

The principle is sound and stronger than the ad-hoc criterion §1 was using. A
competition supplies three things at once that this project otherwise has to
assemble by hand, and §1 kept finding at least one of them missing: a
**curated, versioned, licensed corpus**; a **reference implementation** to
differential-test against; and **published results** that give the
cross-paradigm comparison a baseline it did not compute itself. Essence′ has
no curated corpus (§1.1); SyGuS-IF's competition is dormant and its corpus
unlicensed (§1.6); VMT-LIB and MoXI corpora must be generated (§1.3, §1.4).
Every one of those weaknesses is the absence of a live competition behind the
language.

### 6.1 The second filter the principle needs

Taken alone, "one frontend per competition" admits formats whose corpus is
usable but whose *results are not a baseline*. So this audit applies a second
question to every candidate:

> **Does translating this format to SMT/OMT answer the same question the
> competition asks?**

When the answer is yes, the competition's published results are a legitimate
comparison point and the two-axis `Fidelity` lattice describes the
translation directly. When the answer is no, the corpus is still a source of
formulas, but the competition ranking measures something the translated
instance does not compute — counting, or a strategy, or a termination
proof — and quoting it beside an SMT solving time would be a category error.

This is the same distinction §2 already had to draw for SyGuS-IF and TPTP,
generalised: §2 asked it per language, §6 asks it per competition, and it is
the filter that decides whether a competition is worth a frontend at all.

### 6.2 Competitions covered by the 22-language list

Thirteen, one per row — eleven covered before this section and two added by
§6.3, exactly as §6.4's changelog records. This is an audit, not a proposal;
it exists so that the coverage claim can be checked rather than asserted.

| Competition | Format in our list | Same question? |
|---|---|:--:|
| SAT Competition | DIMACS CNF | yes |
| MaxSAT Evaluation | WCNF | yes |
| Pseudo-Boolean Competition | OPB / WBO | yes |
| QBFEVAL | QDIMACS | yes |
| SMT-COMP | SMT-LIB2 | yes (identity) |
| CHC-COMP | CHC-COMP | yes |
| MiniZinc Challenge | MiniZinc / FlatZinc | yes |
| XCSP3 Competition | XCSP3 | yes |
| HWMCC | BTOR2 / AIGER | yes |
| CASC | TPTP | via §2's negation |
| SyGuS-Comp (dormant since 2019) | SyGuS-IF | **no** — synthesis, see §2 |
| IPC (added by §6.3) | PDDL | yes, at a fixed horizon |
| SYNTCOMP (added by §6.3) | AIGER-EXT safety track | yes, bounded realizability |

MIPLIB backs LP/MPS and Essence′ is backed by Savile Row rather than a
competition; both are libraries, not competitions, and are counted nowhere
above.

### 6.3 Candidates evaluated

#### IPC — International Planning Competition (PDDL) · **add**

| Question | Answer |
|---|---|
| Spec | PDDL 2.1 (Fox & Long, JAIR 20, 2003) for the numeric fragments; classical tracks use the PDDL 2.1 level-1 subset |
| Corpus | IPC 2023 numeric track: **380 tasks across 36 domains**, `ipc2023-numeric.github.io`; classical-track corpora from prior editions are larger and long-archived |
| Reference implementation | Competition planners (the Fast Downward family and the numeric planners entered in 2023) |
| SMT-LIB basis | No — but the concrete syntax is **Lisp-style S-expressions**, so the reader shape is one we already build for SMT-LIB, VMT-LIB and MoXI |
| Same question? | **Yes**, at a fixed horizon |

Planning-as-satisfiability is a thirty-year-old, well-understood encoding, and
critically its loss of fidelity is one this project already models exactly:
a plan found at horizon *k* is a real plan (**sound**), while no plan at
horizon *k* does not mean no plan exists (**incomplete**). That is
`Fidelity::underApprox` with a step bound — structurally identical to BMC,
which cluster D already implements.

Two consequences, both small and both real:

- A new `Bound::Kind::PLAN_HORIZON`. It is semantically the same shape as
  `BMC_DEPTH`, but reporting a planning instance's bound as "BMC depth" would
  mislead a reader of the report, and the report is the product here.
- PDDL fits **cluster D**: predicates and numeric fluents are the state
  variables, grounded actions are the transition relation's disjuncts, the
  goal is the property. One caveat to write down when Plan 4 starts —
  cluster D's `properties` are safety-shaped (BTOR2, MoXI, VMT-LIB all check
  "bad never happens"), whereas a planning goal is **reachability**. These
  are duals, so this is a flag on the property, not a second struct; but it
  must be an explicit flag, because silently unrolling a reachability goal
  through a safety checker inverts the answer.

Cost **1.8×**: grammar ~0.7× (S-expressions, but two files per instance —
domain and problem — which `SourceUnit::data_paths` already supports, as MPS
does), plus a **grounding pass** (instantiating action schemas over the object
universe) that is genuinely new work of roughly cluster A's decomposition-pass
size, plus numeric fluents. Reuses cluster D's `TransitionSystem` and BMC
unrolling pass. **Plan 4.**

#### SYNTCOMP — Reactive Synthesis Competition · **add, at real cost**

| Question | Answer |
|---|---|
| Spec | Two tracks: an **AIGER extension** (safety track; controllable inputs marked in the symbol table) and **TLSF** (LTL track) |
| Corpus | SYNTCOMP benchmark repository, curated per edition; competition is **live** and CAV-affiliated |
| Reference implementation | Competition entrants across realizability and synthesis subtracks |
| SMT-LIB basis | No |
| Same question? | **No** — realizability is ∃strategy ∀environment |

The AIGER-extension track's **parser** is nearly free once AIGER lands: it is
AIGER plus a controllable-input convention. The **encoding is not free**, and
it would be a mistake to plan it as though it were. A safety game is a
two-player, quantifier-alternating problem; translating it to a single
existential SMT query does not answer realizability. Bounded realizability is
expressible — one ∃controllable/∀uncontrollable alternation per step — but
that encoding is the work, and it lands on cluster C's quantifier surface
rather than on the AIGER parser.

Kept anyway, for a reason that emerged from this audit rather than being
assumed going in: **SYNTCOMP is a live competition and SyGuS-Comp is not**
(dormant since 2019, corpus licence unstated, §1.6). If synthesis is to be
one of the domains this project reports on, resting that domain entirely on
SyGuS-IF means resting it on an unmaintained corpus. SYNTCOMP gives the
synthesis domain a corpus that is curated, licensed and current.

Cost **1.5×**: parser ~0.2× marginal over AIGER; the bounded-realizability
∃∀ encoding is the rest. Prerequisites: cluster C (quantifiers, Plan 2) and
AIGER (Plan 4). **Plan 5**, alongside SyGuS-IF, where the two synthesis
languages can share one honest account of what a synthesis "translation"
means. Only the AIGER-extension track is in scope; **TLSF is a separate
language** (LTL specifications) and is not proposed here.

#### Model Counting Competition · **defer, as a DIMACS extension, not a language**

| Question | Answer |
|---|---|
| Spec | Format v1.1, `mccompetition.org` — **DIMACS CNF plus weight and projection statements** carried on `c p` comment lines |
| Corpus | MCC editions 2021–2026; tracks MC / WMC / PMC / PWMC |
| Reference implementation | Competition counters |
| SMT-LIB basis | No (DIMACS) |
| Same question? | **No** — counting, not satisfiability |

This was the clearest case for the §6.1 filter. The parser cost was close to
zero: DIMACS was already parsed, and the extension was two comment-line
conventions (`c t <track>`, and `c p weight` / `c p show`). But an SMT solver
asked about an MCC instance reports whether a model exists; the competition
ranks how fast a counter reports **how many** exist. `Fidelity::preserves_count`
now names that gap: it is the axis for "every model of the source corresponds
to exactly one model of the target", independent of `sound`, `complete` and
`preserves_optimum` — counting is still not a lossy translation of
satisfiability into itself, it is a **different question**, and the DIMACS
lift stays `Fidelity::exact()` because reading the headers does not change
the formula translated.

The residual argument for it was real and is why the extension was taken up:
MCC instances are selected to be *hard to count*, which is a different
hardness profile from SAT Competition instances, so as a pure formula corpus
they are not redundant. That argument justified extending the DIMACS
frontend to read and record the weight and projection lines — it did not
justify a 23rd entry in the language list, and still does not. **Taken up as
a conditional extension of the Plan 2 DIMACS frontend**: the frontend now
reads `c t <track>`, `c p weight <lit> <w> 0` and `c p show <vars> 0`,
recording what it reads rather than discarding it, and refuses an
unrecognised `c p <directive>` by name. The conclusion is unchanged, and
unchanged for the same reason: an MC instance is a plain `.cnf`; what makes
it an MC instance is the question asked of the file, not the file.

#### SV-COMP · **decline**

33 353 verification tasks (2025 edition), 6 specifications, corpus at
`gitlab.com/sosy-lab/benchmarking/sv-benchmarks` tagged per edition — by a
wide margin the largest corpus considered anywhere in this document. Declined
regardless, because the input is **C source code**. Translating C to SMT is
writing a verifier: it requires a memory model, pointer aliasing, loop
invariants and undefined-behaviour semantics, which is the entire content of
CBMC and CPAchecker rather than a frontend. This is the same boundary the
design spec's §2.3 already draws for Verilog, applied consistently.

Worth recording that the domain is not therefore absent: SV-COMP tasks reach
SMT through CHC (SeaHorn and similar) and through BMC, and **CHC-COMP is
already in the list** — so program verification is represented by the
intermediate format the tools actually produce rather than by their source
input. Boogie (§1.5) covers the same domain from the verification-condition
side.

#### TermCOMP and CoCo · **decline**

TermCOMP (TPDB / WST format, `github.com/TermCOMP/TPDB`) and the Confluence
Competition (COPS format; TRS / CTRS / MSTRS / HRS) both have real corpora and
live competitions. Both fail the §6.1 filter more fundamentally than model
counting does: termination and confluence of a rewrite system are not
expressible as a single SMT query at all. The connection runs the other way —
termination provers *call* SMT solvers to discharge ordering constraints they
generate internally. A frontend here would have to be a termination prover
that happens to emit SMT, which is a different project.

### 6.4 Net effect on this document

**20 → 22 languages**, one new `Bound::Kind`, no new cluster.

| Change | Where |
|---|---|
| PDDL added to cluster D | §3.1 cluster D language list; §3.2 at 1.8×; §4 table, Plan 4 |
| SYNTCOMP (AIGER-EXT) added, spanning clusters C and D | §3.1 clusters C and D; §3.2 at 1.5×; §4 table, Plan 5 |
| `Bound::Kind::PLAN_HORIZON` | design spec §4.1; `include/somtparser/translation/fidelity.h` when Plan 4 starts |
| Cluster D `properties` need a safety/reachability flag | §6.3, to be written into Plan 4's first task |
| MCC as a conditional DIMACS extension | §6.3; no language-list entry |
| Competition coverage: 11 → 13 | §6.2 |

Both additions land in plans that already exist and already own their
prerequisite clusters, so neither creates a new plan or reopens §4.2's
bit-vector scheduling decision.
