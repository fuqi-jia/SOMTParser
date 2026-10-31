# AIGER — bit-level hardware model checking

**Date**: 2026-08-25
**Status**: **implemented for both encodings** (`languages/aiger/`): the ASCII `aag` form
and, since 2026-09-19, the binary `aig` form — inputs and latch literals are implicit, the
AND-gate right-hand sides are decoded from non-increasing variable-length deltas, and a file
whose deltas do not decrease is rejected as corrupt (§2.4). Liveness remains refused.

[Typed module import](../module-import.md) preserves the circuit without requiring
a bad property or unrolling depth. An empty circuit is a valid module; it still
does not supply a reachability query to `translate`.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster **D**, §3.2, §4, §6.3
(SYNTCOMP's safety track uses an AIGER extension — `syntcomp.md`).

<!-- proposed-hir: ExprKind::NEXT, Op::IFF -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

<!-- implicit-constraints:
  a latch with no reset column => reset to 0 by the AIGER specification; only an explicit reset equal to the latch's own literal is uninitialised (§2.3, §4.2)
  every latch => carries its value across the step boundary; the transition relation must state NEXT(l) = <its next literal> for every latch, not only for the ones an encoder finds interesting (§2.3)
  an input => a fresh unconstrained value at every step, so unrolling introduces one variable per input per step (§2.3)
  literal 0 is constant FALSE and literal 1 is constant TRUE => not variable indices; index 0 does not exist as a variable (§2.2)
  an even literal 2v is the positive occurrence of variable v and 2v+1 its negation => the low bit is a negation flag, not part of the index (§2.2)
  binary format: an AND gate's rhs literals are stored as DELTAS from the gate's own literal and are non-increasing => decoding must add them back, and the ordering constraint is what makes the delta encoding unambiguous (§2.4)
  a bad/output property asks reachability at any depth => a bounded translation answers only "within k", which Bound::BMC_DEPTH records (§4.1)
  invariant constraints for a bad-state witness => hold from step 0 through and including the witness step, not necessarily through the end of a longer fixed unrolling (§2.3, §4.1)
  an extended 1.9 header, even with B=0 => outputs remain observations and are not reinterpreted as old-format safety properties (§2.1)
-->

**Headline result of the audit in §4**: the implemented ASCII adapter unrolls directly into
`ConstraintModel` and records `underApprox(BMC_DEPTH=k)`. Its source-specific obligations are
literal identity, exact reset defaults, old-versus-extended property selection, constraint
prefixes, and structural validation. Liveness remains refused.

The finding worth the document is not a bug but a **measurement** question (§4.3), and it is
the one this format raises more sharply than any other: AIGER is **bit-level**. Every state
is one bit, every gate is a two-input AND. The SMT translation of an AIGER circuit is
therefore a *propositional* formula — it uses no theory at all. So an AIGER arm measures SMT
solvers on SAT problems, against HWMCC entrants that are specialised bit-level model
checkers running IC3/PDR. The translation is faithful and the comparison is close to
meaningless unless it is framed as what it is: a measurement of the *overhead* of routing a
SAT problem through an SMT solver, which is a legitimate and much narrower claim.

---

## 1. What the format is

AIGER is a format for And-Inverter Graphs: sequential circuits built from two-input AND
gates, inverters and latches. It is the bit-level lingua franca of hardware model checking
and the input of HWMCC's bit-level track.

Two encodings share one semantics: **ASCII** (`.aag`) and **binary** (`.aig`). The binary
form is much smaller and is what corpora ship.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| AIGER 1.9 and Beyond | 2011 draft; defines reset, property and constraint semantics | <https://fmv.jku.at/hwmcc12/beyond1.pdf> |
| AIGER 20071012 format report | inherited ASCII/binary syntax and validity rules | <https://fmv.jku.at/papers/Biere-FMV-TR-07-1.pdf> |
| `aiger` reference implementation | parser, checker and tools | <https://github.com/arminbiere/aiger> |

The old-versus-extended distinction is semantic: only a header without the optional suffix
uses outputs as safety properties. An extended header with explicit `B=0` has no bad-state
query, even if it contains ordinary outputs.

SYNTCOMP's safety track uses an AIGER **extension** in which inputs are partitioned into
controllable and uncontrollable by a name prefix; that is a different problem and
`syntcomp.md` is its document. `docs/languages-scoping.md` §3.2 costs SYNTCOMP at 1.5×
precisely because the parser is nearly free here and the *encoding* is not.

---

## 2. Semantics — what a file means

### 2.1 The header

```
aag M I L O A [B C J F]
```

`M` maximum variable index, `I` inputs, `L` latches, `O` outputs, `A` AND gates, and in 1.9
`B` bad states, `C` constraints, `J` justice properties, `F` fairness constraints. `aig` for
binary, `aag` for ASCII.

### 2.2 Literals

A **literal** is `2·v` for the positive occurrence of variable `v` and `2·v + 1` for its
negation. Literal `0` is constant FALSE and `1` is constant TRUE; variable index 0 does not
exist.

This is the format's one piece of bit-twiddling and it is the most likely first bug: the low
bit is a *negation flag*, not part of the index. A reader that treats literals as indices
silently reads a circuit in which every negated occurrence refers to the wrong variable.

### 2.3 Sections

| Section | ASCII form | Meaning |
|---|---|---|
| Inputs | one literal per line | unconstrained, **fresh at every step** |
| Latches | `<current> <next> [<reset>]` | a one-bit state; `reset` is 1.9 and optional |
| Outputs | one literal per line | observation; in 1.0 also the safety property |
| AND gates | `<lhs> <rhs0> <rhs1>` | `lhs = rhs0 ∧ rhs1` |
| Bad (1.9) | one literal per line | reachability property |
| Constraints (1.9) | one literal per line | holds from step 0 through the bad-state witness step |
| Justice / Fairness (1.9) | literal groups | liveness (`btor2.md` §4.5) |

Latch reset values in 1.9 are `0`, `1`, or the latch's own literal meaning "uninitialised".
If the optional column is absent, the specified default is `0`; its absence does not prove
that the file predates 1.9. §4.2.

### 2.4 The binary encoding

The `.aig` form drops the input and AND-gate literal lists and reconstructs them: inputs are
implicitly `2, 4, …, 2I`; AND gate *i* has lhs `2(I+L+i)`; and each gate's two rhs literals
are stored as **variable-length deltas** from the gate's own literal, non-increasing.

The non-increasing requirement is what makes the encoding unambiguous, and it is also a
validity check a reader gets for free — a file whose deltas do not decrease is corrupt, and
saying so beats decoding it into a plausible wrong circuit.

### 2.5 What a solution is

A witness trace of input values reaching a bad state, or a proof that none exists. `aigsim`
replays a witness, so model-level differential validation is available, as with BTOR2
(`btor2.md` §2.5) and unlike QBF (`qdimacs.md` §2.4).

---

## 3. Construct → HIR mapping

The current frontend performs bounded unrolling while constructing ordinary typed HIR. The
transition-system identity and bound survive in the semantic contract and translation report.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| input | fresh `Bool` declaration at each step | none | `exact()` within the bound |
| latch | one `Bool` per step plus `l@(i+1) = next(l)@i` | none | `exact()` within the bound |
| latch reset `0`/`1`, including omitted-column default | a step-0 assertion | none | `exact()` |
| **reset equal to the latch literal** | **no step-0 assertion** (§4.2) | none | `exact()` |
| AND gate | `Op::AND` over the two operands | none | `exact()` |
| negated literal | `Op::NOT` | none | `exact()` |
| literal `0` / `1` | `mkBool(false)` / `mkBool(true)` | none | `exact()` |
| output (old safety form) | member of the step-wise reachability disjunction | none | §4.1 |
| bad (extended form) | member of the prefix-guarded reachability disjunction | none | §4.1 |
| constraint (1.9) | conjoined through each candidate witness step | none | `exact()` |
| justice / fairness (1.9) | **refused before lowering** | lasso support required | — |
| symbol table / comments | ignored because they do not alter circuit semantics | none | `exact()` |

Everything in the combinational half is `Op::AND` and `Op::NOT` over Booleans, both of which
the HIR already has. **AIGER needs no new operator at all** — its entire new surface is
cluster D's structure.

---

## 4. Semantic gaps and encoding choices

### 4.1 BMC, shared with the rest of cluster D

Identical in mechanism and consequence to `btor2.md` §4.2: unroll to depth *k*, a SAT answer
is a genuine counterexample, an UNSAT answer is `underApprox` with `Bound::BMC_DEPTH`
(`include/somtparser/translation/fidelity.h:90`, `:134`). The k-induction option and the
report-the-two-halves-separately recommendation apply unchanged, and are not repeated here.

One AIGER-specific note: because every state is a single bit, the unrolled formula's size is
`k · (latches + gates)` with a small constant — no bit-vector blow-up, no array copies
(`btor2.md` §4.4). AIGER is the cheapest cluster-D language to unroll, which makes it the
right one to **validate the unrolling pass against**: if a BMC bug exists, it shows up here
without bit-vector or array reasoning obscuring it. Same argument as `qdimacs.md` §5's for
cluster C.

### 4.2 Latch reset values

| Case | Meaning | What `init` gets |
|---|---|---|
| reset `0` or `1` | initialised | `l@0 = <value>` |
| reset = its own literal | **uninitialised** | **nothing** |
| reset column absent | specified default `0` | `l@0 = false`; exact default recorded |

The middle row is `btor2.md` §4.3's "no `init` line" trap in AIGER clothing, and it fails in
the same direction: defaulting an uninitialised latch to 0 **removes** initial states, so an
unsafe circuit can be reported safe. **Incomplete, silent.**

The third row is not an approximation or guessed version. It is a source-language default and
therefore belongs in the automatically added assumptions `A_Σ`. The report records that the
default was applied, with exact fidelity. Treating absence as uninitialised would instead add
initial models and invent counterexamples.

### 4.3 Property selection and constraint prefixes

For each candidate witness step `i`, the reachability formula is
`c@0 ∧ ... ∧ c@i ∧ bad@i`; candidates for `0..k` are disjoined. Globally asserting
constraints through step `k` incorrectly removes a shorter valid witness if a constraint fails
after the bad step. Outputs are candidates only for an old header with no `B C J F` suffix.

### 4.4 What an AIGER arm actually measures

Every AIGER value is one bit. The translated SMT script contains no theory: only Boolean
variables, `and`, `not`, and — after unrolling — a lot of them. It is a SAT instance written
in SMT-LIB syntax.

That makes the comparison against HWMCC entrants a comparison between a general-purpose SMT
solver's SAT core and a specialised bit-level model checker running IC3/PDR with
circuit-aware preprocessing. The result is predictable and uninformative as stated.

Three framings that are informative, in increasing order of usefulness:

| Framing | Claim | Fair? |
|---|---|---|
| "SMT versus HWMCC solvers on AIGER" | none worth making | no |
| "the overhead of routing a SAT problem through an SMT frontend" | measures the translation's cost, not the solver's ability | yes, and narrow |
| **"BMC via SMT versus BMC via SAT, same depth, same circuit"** | isolates the solver from the algorithm by holding the algorithm fixed | **yes** — and it is the one an AIGER arm can support |

The third is the recommendation. It also needs no new machinery: `aigunroll` or an
equivalent produces the SAT instance for the same depth, and `dimacs-cnf.md`'s arm already
covers the SAT side.

This is `docs/languages-scoping.md` §6's second filter applied to a format that *passes* it
— the question is preserved exactly — and still yields a result that must be framed
carefully. Worth recording, because the second filter is usually discussed as a pass/fail
gate and this is a case where passing is not sufficient.

### 4.5 Parser validity and the binary corpus

The ASCII reader validates exact section counts, unsigned fields, definition uniqueness,
literal bounds, reset alternatives, reference definedness and acyclic AND dependencies.
Previously, an undefined literal became an undeclared-looking fresh HIR identifier, which
strictly enlarged the target model class. **The binary delta decoder is implemented
(2026-09-19)**: implicit input/latch literals are reconstructed, the non-increasing-delta
validity check of §2.4 is enforced, and a truncated or overflowing delta is `E_PARSE`,
never a plausible wrong circuit. `test_aiger.cpp` pins the two encodings to byte-identical
output for the same circuit, so a decoding bug shows up as a differential mismatch.

Corpora ship `.aig`, so a frontend that reads only `.aag` cannot see the corpus. Converting
with `aigtoaig` first is possible but adds a tool to the pipeline; reading binary directly is
cheap enough that it is the better choice.

### 4.6 Liveness, refused

`justice` and `fairness` need a lasso encoding, and `btor2.md` §4.5 argues why refusing them
specifically — rather than refusing the file — is the right first step, and why
`pddl.md` §5's `Property` already separates the fields so a frontend can. Nothing to add.

---

## 5. New HIR surface this format forces

| Surface | Cluster | Also needed by |
|---|---|---|
| **`TransitionSystem`** and `Property` | **D** | BTOR2, VMT-LIB, MoXI, PDDL — specified in `pddl.md` §5 |
| **`ExprKind::NEXT`** | D | the whole of cluster D |
| a BMC unrolling pass recording `Bound::BMC_DEPTH` | D | the whole of cluster D |
| `Op::IFF` | — | convenience for `NEXT(l) ⟺ e`; expressible as two implications or an `EQ` over Bools today |

**Nothing else.** No new sort, no new literal, no arithmetic, no arrays, no quantifiers.
AIGER's combinational half is `Op::AND` and `Op::NOT` over `SortKind::BOOL`, all of which
the HIR has (`include/somtparser/hir/hir.h`).

That makes AIGER the **cheapest member of cluster D** and the natural first implementation
of it, for the same reason `qdimacs.md` §5 argues QDIMACS should be cluster C's: a bug in
the shared machinery has one suspect here and several in BTOR2 (bit-vectors, arrays) or MoXI
(composition).

---

## 6. Fidelity summary

**Exact — the combinational half, entirely.** Literals, negation, AND gates, constants,
inputs, latches, the transition relation, environment constraints, and the properties as
stated.

**`underApprox` — the sequential half.** BMC to depth *k* carries `Bound::BMC_DEPTH` (§4.1).
Cheaper to unroll than any other cluster-D language, but the bound is the same claim.

**Refused, not approximated**: `justice` and `fairness` (§4.5).

**Inherently lossy: nothing.**

**Ways to make it wrong by mistake**:

- Treating a literal as a variable index and losing the negation bit (§2.2). **Reads a
  different circuit.**
- Defaulting a 1.9 uninitialised latch to 0 (§4.2). **Incomplete: reports safe for an unsafe
  circuit.**
- Treating an omitted reset column as uninitialised instead of the specified default 0 (§4.2).
- Requiring 1.9 constraints after the bad-state witness step (§4.3). **Incomplete: can erase
  a valid shorter witness.**
- Treating outputs in an extended header with `B=0` as old-format bad properties (§4.3).
- Accepting undefined literals, duplicate definitions or cyclic AND gates. **Changes the
  source signature or invents target models.**
- Omitting `NEXT(l) = e` for any latch (`btor2.md` §4.3). **Unsound: invents
  counterexamples.**
- Reusing one variable for an input across steps (§2.3).
- Decoding a corrupt delta sequence instead of rejecting it (§4.4). **A plausible wrong
  circuit.**
- Reading a 1.9 file with a 1.0 reader and losing the `bad`/`constraint` sections (§1).
- Counting a bounded UNSAT as "solved" against IC3/PDR results (§4.1, §4.3). **Not a
  fidelity error — a reporting one.**

---

## 7. References

**Format**

1. Biere, Heljanko, Wieringa, [AIGER 1.9 and Beyond](https://fmv.jku.at/hwmcc12/beyond1.pdf), 2011.
2. Biere, [The AIGER And-Inverter Graph Format Version 20071012](https://fmv.jku.at/papers/Biere-FMV-TR-07-1.pdf).
3. [AIGER reference implementation and tools](https://github.com/arminbiere/aiger).

**Competition and corpus**

4. Hardware Model Checking Competition, bit-level track. Instance counts and licence terms
   **not re-confirmed**.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster D), §3.2, §4 (Plan 2), §6 (the second filter,
   which §4.3 shows is necessary but not sufficient), §6.3 (SYNTCOMP's AIGER extension).
6. `docs/languages/pddl.md` §5 (the `TransitionSystem` and `Property` shape).
7. `docs/languages/btor2.md` §4.2 (BMC and its `Bound`), §4.3 (absent transition functions),
   §4.5 (liveness), §2.5 (witness replay).
8. `docs/languages/syntcomp.md` (the AIGER extension, and why its encoding is not cluster D
   at all).
9. `docs/languages/qdimacs.md` §5 (the same "implement the cluster against its simplest
   member" argument, for cluster C).
10. `docs/languages/dimacs-cnf.md` (the SAT arm §4.4's recommended framing compares against).
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`.
