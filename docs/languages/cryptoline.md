# CryptoLine — verifying low-level cryptographic arithmetic

**Date**: 2026-08-25
**Status**: **implemented for the typed scalar core, including cuts and procedures**
(`languages/cryptoline/`, `test/languages/test_cryptoline.cpp`): 14/15 semantic families and
all 17 official `examples/tests` fixtures translate. The implementation follows the official
AST/QF_BV/safety rules for typed atoms, carries and borrows, multiplication, shifts and
rotations, split/join, `cast`/`vpc`, SSA, assertions, range predicates, and instruction safety.
2026-09-20 added the explicit `u*`/`s*` signedness variants with `set`/`clear`/`nop` (the
prefix selects the unsigned/signed reading and the operands must carry it already —
`parsers/common.ml` hints the destination at `typ_to_unsigned`/`typ_to_signed` and
`typecheck/std.ml` `check_same_typ` does the rest), the remaining manual-catalogued
predicate forms: range `udiv`/`sdiv` (§4.5), range-predicate negation/disjunction and prefix
comparisons, the modular-equality suffixes `(mod m)`/`(umod m)`/`(smod m)`/`(srem m)`, the
`eqmod` modulus list, range `const`, `sq`/`pow`/expression-`**`, `adds`/`muls` lists, `poly`,
`ulimbs`/`slimbs` with the official extend-and-sum range construction, and the `intN` type
spelling — and **cut fragmentation** (§2.3, §4.4): `cut`/`ecut`/`rcut` split the verification
into fragments, each refuted under only the previous cut's predicates, with the fragments'
branches disjoined into the one query and `check_index` (the VMT/MoXI selector idiom)
exposing a single fragment as a measurable unit; the fact-selecting prove-with hints
(`precondition`, `cuts [i]`, `all cuts/assumes/ghosts`) are honoured and the solver-selection
hints stay operational. `eassert`/`rassert` assert one side only. 2026-09-20 also added
**procedures and the ghost layer**: a program is a sequence of procedure declarations with
`main` as the entry point (a single-procedure file verifies that procedure); `call` is the
contract (assert the precondition, havock the outputs, assume the postcondition, with inout
actuals' entry values captured by fresh ghosts), `inline` splices the body with formals bound
to actuals (no local renaming, as `Options.Std.rename_local` defaults false — SSA versioning
makes textual splicing exact), and `inlinespec` is the body havocked plus the contract;
`ghost` declares specification-only logical constants whose predicate is always assumed, with
the official disjointness/mention checks. Refused by name: vector forms (`%v`, `uint64[4]` —
an implementation extension the manual's grammar does not define) and named integer constants
(`const id = ...`, `$id`).
**Correctness turns on the `bv2nat` / `bv2int` choice**: the algebraic half is integer
arithmetic over bit-vector values, and declared signedness is the evidence for the lift.
**Scoping context**: `docs/languages-scoping.md` §3.1 clusters **F + H**, §3.2, §4.

<!-- proposed-hir: Op::CONCAT, Op::EXTRACT, Bound::LOOP_UNROLL -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

<!-- implicit-constraints:
  every variable has a declared bit WIDTH and signedness => an operation's result wraps at that width, so a translation to unbounded Int is not a relaxation but a different arithmetic; the width is part of every operation, not an annotation on it (§2.2, §4.2)
  `adds`/`addr`-style instructions produce a CARRY as a second output => the carry is data the program then uses, so dropping it loses a value the rest of the program depends on (§2.2)
  every partial machine instruction has a SAFETY predicate => verification includes each safety condition at its source prefix; omitting these conditions accepts unsafe executions (§2.2)
  `subc`/`subs` returns NOT-borrow while `subb` returns borrow => conflating the flags changes later arithmetic even though both have one-bit type (§2.2)
  `split` extends both outputs to the source width while `spl` returns narrow pieces => conflating them changes the signature as well as the value relation (§2.2, §4.3)
  `vpc` is a cast plus equality of source and target INTEGER interpretations => translating it as cast alone drops a proof obligation (§2.2, §4.3)
  an `assume` in the ghost layer => a hypothesis the proof may use, so it must be asserted as an antecedent rather than checked; confusing assume with assert makes the verification vacuous (§2.3)
  a `cut` => splits the proof into independent obligations, so each fragment's postcondition becomes the next fragment's precondition and translating only the fragments loses the chaining (§2.3, §4.4)
  a `u*`/`s*` instruction prefix selects the unsigned or signed reading of its base instruction => the operands must already carry that signedness, because it decides the safety predicate and the Int lift; coercing an operand would answer a different instruction (§2.2)
  range `udiv`/`sdiv` are machine divisions => they map directly onto `bvudiv`/`bvsdiv`, including the total behaviour at a zero divisor (§4.5)
  a `ghost` declaration's predicate => always ASSUMED, never checked; the ghost variables are specification-only logical constants, disjoint from program variables, and every conjunct of the predicate must mention one of them (§2.3)
  a `call` => the callee's precondition is an OBLIGATION at the call site and its postcondition an ASSUMPTION over havocked outputs, with an inout actual's entry value captured by a fresh ghost; `inline` instead splices the body, so conflating the two answers a different question (§2.3)
  the program is straight-line SSA after unrolling => each assignment defines a new version, so a translation that reuses one variable per name conflates distinct values (§2.2)
-->

**Headline result of the audit in §4**: CryptoLine's own verification is **not pure SMT**,
and that is the whole finding (§4.1). Its range predicates (`rng`) go to an SMT solver and
its algebraic predicates (`eqn`) go to a **computer algebra system** — the hard instances,
the ones the tool exists for, are the algebraic half. An SMT-only translation therefore
either blows up on exactly the instances that matter or answers a different question, and
`docs/languages-scoping.md` §6's second filter applies in the same way it does to SyGuS-IF
(`sygus-if.md` §4.1): the corpus is usable, and the tool's own results are not a baseline
for an SMT-only arm.

That is not a reason to skip it. CryptoLine has the batch's **most application-realistic
corpus** — field arithmetic from OpenSSL and NIST PQC implementations, code that ships — and
an SMT arm over its *range* half is a genuine, well-defined and comparable measurement
(§4.1). The recommendation is to say which half is being measured, in the results, rather
than to report a CryptoLine arm as though it covered the tool's remit.

The second finding is structural and cheap: CryptoLine is cluster H's *small* instance
(§4.4). Boogie's VC generation is weakest-precondition over arbitrary control flow;
CryptoLine's is straight-line SSA with explicit cut points. Same pattern, an order of
magnitude less machinery — which makes it the better place to build cluster H first.

---

## 1. What the format is

CryptoLine is a domain-specific language and verification tool for **low-level
cryptographic arithmetic**: the multi-precision field operations at the core of elliptic
curve and post-quantum implementations, written close to the assembly they model.

Its purpose is narrow and its corpus is the reason it is in this batch: real primitives from
OpenSSL, BoringSSL and NIST PQC submissions, verified against their mathematical
specifications.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| CryptoLine reference implementation and `doc/cryptoline.pdf` | repository inspected 2026-08-25 | [fmlab-iis/cryptoline](https://github.com/fmlab-iis/cryptoline) |
| Typed CryptoLine | CCS 2019 | [DOI 10.1145/3319535.3354199](https://doi.org/10.1145/3319535.3354199) |

The executable semantic oracle used in this audit is the official repository: instruction
graphs come from `qfbv/common.ml`, safety conditions from `verify/smt.ml`, well-formedness
from `typecheck/std.ml`, and syntax/meaning from `doc/cryptoline.pdf`.

### Corpus

Verified cryptographic primitives distributed with the tool and in the associated papers.

| Property | Consequence |
|---|---|
| **Real shipping code** | the most application-realistic corpus in the batch; a result here says something about practice |
| No competition, no ranking | `docs/languages-scoping.md` §7's first filter fails on the baseline leg, as for Boogie (`boogie.md` §1) and Essence′ (`essence-prime.md` §1) |
| CryptoLine itself is the reference | so it is the oracle — but only for the half an SMT arm reproduces (§4.1) |
| Small (tens of programs, not thousands) | statistical claims are not available; per-instance analysis is |

---

## 2. Semantics — what a file means

### 2.1 Shape

```
proc mul_add (uint64 a, uint64 b, uint64 c) =
{ true && true }
mull carry prod a b;
adds overflow sum prod c;
{ eqn sum + overflow * 2**64 = a * b + c && rng true }
```

A procedure with a precondition, a straight-line instruction sequence, and a postcondition.
Both conditions have two halves separated by `&&`: an **algebraic** part (`eqn`) and a
**range** part (`rng`).

### 2.2 Instructions

The instruction set mirrors machine arithmetic:

| Group | Examples | Note |
|---|---|---|
| Move / select | `mov`, `nondet`, `cmov` | `nondet` is a fresh unconstrained SSA value |
| Add / subtract | `add[s]`, `adc[s]`, `sub[c/b]`, `sbc[s]`, `sbb[s]` | `subc` exposes no-borrow; `subb` exposes borrow |
| Multiply | `mul[s]`, `mull`, `mulj` | half, two-output full, and joined double-width results |
| Split / join | `split`, `spl`, `join`, `cast`, `vpc` | `split` extends; `spl` is narrow; `vpc` adds value preservation |
| Bitwise / shift | `and`, `or`, `xor`, `not`, shifts, combined shifts, `rol`/`ror` | output forms retain shifted-out bits as data |
| Comparison | `seteq`, `setne` | result is all ones or all zeros at destination width |

Every variable has a declared **width and signedness** (`uint64`, `sint32`, …), and every
operation has a bit-vector graph at that width. Unsuffixed `add`, `sub`, `mul`, and non-output
shifts also generate separate safety obligations. Their output forms retain overflow or lost
bits as data and therefore do not assert that no such bits exist.

The carry/borrow outputs, split/join identities, and safety conditions are all values or
sentences the translation can silently lose. The implementation derives them from the
official OCaml lowering rather than from mnemonic names.

### 2.3 The ghost layer

`assume`, `assert`, `cut`, and ghost variables. `cut` is the distinctive one: it splits the
verification into independent fragments, each proved separately, with a fragment's
postcondition becoming the next fragment's precondition. It is how CryptoLine keeps
proof obligations tractable on long instruction sequences, and it is a *proof structure*
rather than a program construct.

### 2.4 What a solution is

CryptoLine reports whether the postcondition follows from the precondition and the
instruction sequence. Internally:

- **`rng` predicates** — range and bit-level facts — go to an **SMT solver** (bit-vector
  theory);
- **`eqn` predicates** — modular polynomial identities — go to a **computer algebra system**,
  via Gröbner-basis / ideal-membership reasoning.

§4.1 is about that split.

### 2.5 Source Institution and translation construction

For this adapter, the source logic is a program-verification Institution rather than a set
of free-standing bit-vector formulas:

- **Sign** contains scalar word types, procedure parameters, program variables, and their
  SSA-renamed definitions.
- **Sen** contains the precondition, each instruction graph, each instruction-safety
  condition, source assertions, and the final postcondition. Algebraic and range halves are
  distinct sentence forms.
- **Mod** is a finite typed valuation trace over the straight-line program, together with
  the mathematical integer interpretation selected by each word's signedness.
- **Satisfaction** requires the precondition and instruction graph, and requires every safety,
  assertion, and postcondition obligation at its own source prefix. `Cost` and its order are
  empty; observables are source variables and the failing obligation location.

The executable adapter is `(Phi,A,alpha,beta,h)`:

- `Phi` maps `uintN`/`sintN` storage to `BitVec N`, creates fresh SSA symbols, and maps an
  algebraic occurrence to `bv2nat`/`bv2int` according to its declaration.
- `A` contains instruction graph equalities, preconditions, preceding assumptions, and
  explicit safety relations. It does not contain proof-strategy annotations.
- `alpha` maps every obligation at prefix `i` to `prefix_i AND NOT obligation_i`, then
  disjoins those branches. This preserves an earlier counterexample even if a later
  `assume false` makes the remaining path unreachable.
- `beta` decodes a satisfying target valuation to the corresponding source SSA trace and
  removes generated versions when presenting source variables. `h` is the unique empty
  objective mapping.

Consequently, target `SAT` means **a source-level counterexample exists**, while target
`UNSAT` means no encoded safety/assertion/postcondition counterexample exists. This decision
polarity is recorded by the semantic contract; it must not be inferred from formula shape.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as extended by cluster **F** (bit-vectors) and produced by a
cluster **H** pass (§4.4). As with `boogie.md` §3, the frontend's product is a *verification
condition*, not a transliteration — but unlike Boogie's, the VC here is close to the program
text, because the program is straight-line.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| `uint64 x` etc. | a `VarDecl` of a width-parameterised bit-vector sort | **`SortKind::BITVEC`** | `exact()` |
| an SSA assignment | a fresh `VarDecl` version plus an equality `Constraint` | none beyond the sort | `exact()` |
| `add`, `sub`, `mul`, bitwise, shifts | the corresponding bit-vector operators | cluster F | `exact()` |
| instruction safety | a separately negated obligation under the exact source prefix | cluster H | `exact()` |
| `adds`/`adcs` carry output | an extra `VarDecl` and its defining equality | cluster F | `exact()` |
| `mull` double-width product | two `VarDecl`s plus the identity relating them | cluster F, `Op::CONCAT` | `exact()` |
| `split` / `spl` / `join` / `cast` | exact extract/extend/concat assignment graph | `Op::EXTRACT`, `Op::CONCAT` | `exact()` |
| `vpc` | cast graph plus equality of signed/unsigned integer interpretations | BV-to-Int operators | `exact()` |
| `nondet` | a fresh unconstrained `VarDecl` | none | `exact()` |
| `assume` (ghost) | an antecedent of the VC | none | `exact()` |
| `assert` (ghost) | a proof obligation | none | `exact()` |
| `cut` | fragment boundary: the VC becomes several refutation branches, tagged per fragment and disjoined; `check_index` selects one (§4.4) | cluster H | `exact()` |
| `ghost g : p` | a fresh `VarDecl` per ghost plus the predicate as an antecedent; ghosts never appear as instruction operands | none | `exact()` |
| `proc` declaration | registered; the body validated in a scratch scope, the contract recorded over the formals | none | `exact()` |
| `call p(...)` | assert the substituted precondition, havock the outputs, assume the substituted postcondition; inout entry values captured by fresh ghosts | cluster H | `exact()` |
| `inline p(...)` | the body re-translated at the call site with formals bound to actuals | cluster H | `exact()` |
| `inlinespec p(...)` | `call` plus nondet over the body's assigned variables | cluster H | `exact()` |
| **`rng` predicate** | a bit-vector `Constraint` | cluster F | `exact()` |
| **`eqn` predicate** | mathematical `Int` polynomial equality or existential divisibility | BV-to-Int operators | `exact()`; may be expensive |

---

## 4. Semantic gaps and encoding choices

### 4.1 The tool is not an SMT tool, and the hard half is the other one

CryptoLine's architecture is a deliberate split (§2.4), and it exists because the two halves
are hard in different ways:

| Predicate | Reasoning | Why |
|---|---|---|
| `rng` | SMT, bit-vector theory | bounds, overflow, bit patterns — decidable and bit-blastable |
| `eqn` | computer algebra (Gröbner basis / ideal membership) | polynomial and modular identities over mathematical integer readings |

This frontend maps an `eqn` obligation exactly to nonlinear integer arithmetic, using
`bv2nat`/`bv2int` only at the machine-word boundary and an existential multiplier for
`eqmod`. The issue is practicality, not fidelity: the native tool routes these obligations
to algebra systems because generic SMT reasoning over large polynomial identities is often
the wrong method.

| Framing | Claim | Fair? |
|---|---|---|
| "SMT versus CryptoLine on its corpus" | none | **no** — CryptoLine did not use SMT for the hard half |
| "SMT on the `rng` obligations" | a well-defined, comparable measurement of the half CryptoLine also sends to SMT | **yes**, and it is directly checkable against CryptoLine's own SMT calls |
| "SMT on the `eqn` obligations" | a measurement of generic SMT nonlinear arithmetic against algebraic reasoning | **yes, with that method difference disclosed** |
| "SMT on everything, reported as a CryptoLine arm" | conflates the two | **no** |

The third row is worth emphasising because it inverts the usual framing: a *negative* result
there is a finding, not a failure. "SMT solvers time out on the obligations CryptoLine routes
to a CAS" is precisely the kind of domain-specific evidence this project set out to gather,
and reporting it as such is more valuable than reporting a low solve rate without the
explanation.

This is `docs/languages-scoping.md` §6's second filter with an unusual resolution: the
question *is* preserved (the obligation is the same logical statement), and the **method**
is not. `sygus-if.md` §4.1 fails the filter on the question's shape; this one fails it on
the reasoning technology, and the two need different disclosure.

### 4.2 Machine words are not integers, and the substitution is not a relaxation

Every CryptoLine value has a width and wraps. The tempting simplification — translate
`uint64` as `Int` with a range constraint — is **wrong in both directions**:

| | machine `uint64` | `Int` with `0 ≤ x < 2^64` |
|---|---|---|
| `a + b` when it overflows | wraps to `a + b − 2^64` | violates the range constraint, so the model is UNSAT |
| the program's intent | overflow is *expected* and the carry captures it | overflow is impossible |
| `a * b` | wraps; `mull` captures the full product | unbounded |

So an `Int` translation makes overflow unsatisfiable rather than wrapping, which turns
programs that rely on wrap-around — i.e. all of them — into infeasible models. This is not
an approximation with a `Fidelity` value; it is a different arithmetic. **Cluster F is a
prerequisite, not an optimisation**, and CryptoLine cannot be attempted before it, unlike
BTOR2 (`btor2.md` §4.1) whose combinational half at least *has* an Int-shaped reading for
small widths.

### 4.3 Split, join and cast must assert their identities

`split hi lo v n` redistributes `v` into `hi` and `lo` at bit `n`. The relation
`v = hi · 2ⁿ + lo`, with `lo < 2ⁿ`, is what the instruction *means*, and it must be asserted.

A translation that declares `hi` and `lo` as fresh variables and does not relate them to `v`
produces a program in which the two halves are arbitrary — **unsound**, and it will "verify"
postconditions that do not hold. This is the same shape as `flatzinc.md` §4.3's missing index
constraint and `lp.md` §4.2's missing implicit bound: a fresh variable introduced without the
constraint that defines it.

`cast` between widths is the same question with truncation or extension semantics, and
`Op::EXTRACT`/`Op::CONCAT` are the natural operators.

### 4.4 Cluster H's small instance

`docs/languages-scoping.md` §3.1 puts Boogie and CryptoLine both in cluster H —
"a frontend-level symbolic-execution / weakest-precondition pass, specific to each language's
control-flow model" — and notes CryptoLine is "a much smaller straight-line SSA instance of
the same pattern". Confirmed, and worth acting on:

| | Boogie | CryptoLine |
|---|---|---|
| control flow | arbitrary (`goto`, loops, calls) | **straight-line instruction trace** |
| procedure calls | contracts, two-sided (`boogie.md` §4.2) | present, and simpler |
| proof structure | one VC per procedure | **several, at `cut` points** (§2.3) |
| VC generation | weakest precondition over a CFG | SSA plus conjunction |

**Build cluster H here first.** The pattern is the same and the machinery is a fraction of
Boogie's, which is the same "implement the cluster against its simplest member" argument
`qdimacs.md` §5 makes for cluster C, `aiger.md` §5 for cluster D and `sygus-if.md` §4.4 for
cluster I. Four clusters, four times the same conclusion — the pattern is now regular enough
to be a rule for Plan 2's sequencing rather than four separate observations.

The `cut` mechanism is the one thing CryptoLine adds that Boogie does not have, and it is
*helpful* rather than costly: each fragment is an independent, smaller SMT query, which is
exactly the granularity an experiment wants. **Implemented 2026-09-20**: a `ConstraintModel`
is one query, so the frontend emits one refutation branch per obligation, tagged with its
fragment index, and disjoins the branches — UNSAT iff every fragment verifies. The
`check_index` parse option (the VMT/MoXI per-property selector idiom, B5) restricts the
query to one fragment, giving the separate measurable unit this section asks for. The
chaining is the official one (`ast/cryptoline.ml` `cut_espec`/`cut_rspec`): a fragment's
prefix is the conjunction of the previous cut's same-side predicates and NOTHING else —
the earlier instructions and assumes are not carried (`all assumes`/`all ghosts` hints
re-select those facts explicitly), and `ecut`/`rcut` cut one side and are numbered
separately from 0.

### 4.5 Range division and remainder

CryptoLine range expressions include **machine** division/remainder operators: `udiv`,
`sdiv`, `umod`, `srem`, and `smod`. They are not program instructions. The frontend accepts
all five: the mapping is the one place after BTOR2 (`btor2.md` §2.3) where the convention
needs **no decision** — SMT-LIB's `FixedSizeBitVectors` defines `bvudiv`, `bvsdiv`, `bvurem`,
`bvsrem`, `bvsmod` with exactly the machine semantics, including the total behaviour at zero
(`bvudiv x 0` is all ones; `bvsdiv x 0` is 1 for nonnegative `x`, all ones otherwise).

The mapping is direct, but the reliance on the total-at-zero behaviour belongs in the
assumption profile even though it needs no auxiliary axiom: the frontend records an
`EncodingChoice` (`direct-smtlib-bitvector-division`) the first time each division operator
appears, and the institution profile keeps `division = MIXED` (unsigned floor division and
signed truncation toward zero are both present).

### 4.6 Bit-widths beyond 64

Multi-precision arithmetic is the point: a 256-bit field element is four or eight machine
words, and the *specification* is a statement about the 256-bit value. So the VC mixes
machine-width operations with wide-value identities.

| Approach | Fidelity | Note |
|---|---|---|
| Wide bit-vectors for composed machine values, related by `concat` | `exact()` | direct range-level route |
| Mathematical integer arithmetic for the algebraic half | `exact()` | current route; `eqmod` becomes existential divisibility |

The first row is a design requirement on cluster F worth stating now: **widths are
arbitrary, not machine-sized.** A `SortKind::BITVEC` limited to 8/16/32/64 would not carry
this language, and the engine's own bit-vector kinds are not so limited.

---

## 5. New HIR surface this format forces

| Surface | Cluster | Also needed by |
|---|---|---|
| **`SortKind::BITVEC`**, arbitrary width (§4.6), plus the operator set and `ExprKind::LIT_BITVEC` | **F** | BTOR2; unblocks QF_BV for `smtlib2.md` |
| **`Op::CONCAT`, `Op::EXTRACT`** | F | BTOR2 (`slice`, `uext`, `sext`) |
| a **VC generation pass**, straight-line SSA with future `cut` fragments | **H** | Boogie (the larger instance) |
| `ExprKind::APPLY` | G | only if specifications use uninterpreted functions |

**Not needed**: objectives, arrays, transition systems, comprehensions, real literals.
CryptoLine is narrow, and its two clusters are both shared.

---

## 6. Fidelity summary

**Exact on the accepted scalar core**: widths, wrapping instruction graphs, safety
conditions, carries/borrows, splits/joins/casts, SSA, assumptions/assertions, and the
implemented algebraic/range predicate forms.

**Exact but potentially impractical — the `eqn` obligations** (§4.1). They are nonlinear
integer formulas rather than bit-blasted substitutes. `Fidelity` says `exact()`; solver
resource limits remain an operational result, not an approximation lattice value.

**Blocked, not lossy**: vector forms (`%v`, `uint64[4]` — an implementation extension the
manual's grammar does not define) and named integer constants (`const id = ...`, `$id`) are
refused by name. The explicit signedness variants, the predicate catalogue, cut
fragmentation, and procedures/ghosts are implemented (2026-09-20); the variant prefix is a
typing contract — a `u*` instruction on signed operands is ill-formed
(`typecheck/std.ml`'s `check_same_typ`), never coerced.

**Ways to make it wrong by mistake**:

- Translating machine words as `Int` with range constraints (§4.2). **Makes overflow
  unsatisfiable; the programs rely on it.**
- Introducing `split`/`join`/`cast` outputs without asserting the identity that defines them
  (§4.3). **Unsound: verifies postconditions that do not hold.**
- Dropping a carry output (§2.2). Loses a value the program uses.
- Treating `assume` as `assert` (§2.3). Makes the verification vacuous.
- Translating `cut` fragments without chaining each postcondition into the next
  precondition (§2.3, §4.4).
- Substituting a call's postcondition without capturing an inout actual's entry value in a
  fresh ghost (§2.3): the assumed postcondition then reads the havocked output on both
  sides — collapsing to a tautology (the output stays unconstrained) or to an inconsistent
  assumption that vacuously "verifies" everything after the call.
- Reusing one variable per name instead of per SSA version (§2.2).
- Reporting an SMT-only arm as a CryptoLine result (§4.1). **The tool's hard half does not
  use SMT.**

---

## 7. References

**Tool and language**

1. [Official CryptoLine repository](https://github.com/fmlab-iis/cryptoline), including
   `doc/cryptoline.pdf`, `qfbv/common.ml`, `verify/smt.ml`, and `typecheck/std.ml`.
2. Yu-Fu Fu et al., [Signed Cryptographic Program Verification with Typed
   CryptoLine](https://doi.org/10.1145/3319535.3354199), CCS 2019.

**Corpus**

3. Official `examples/tests` corpus: 17 compact files vendored unmodified under
   `languages/cryptoline/instances/upstream`; provenance records source and MIT licence.

**This project**

4. `docs/languages-scoping.md` §3.1 (clusters F and H, and the "much smaller straight-line
   SSA instance" note §4.4 confirms), §3.2, §4 (Plan 2), §6 (the second filter, resolved
   here on *method* rather than on question shape), §7 (the competition audit).
5. `docs/languages/btor2.md` §4.1 (cluster F, and the width-parameterised sort §4.6 adds a
   requirement to), §2.3 (the other language whose division convention needs no decision).
6. `docs/languages/boogie.md` §3 (the same VC-not-a-mapping structure), §4.3 (the loop
   bound), §4.2 (contracts, the larger version of §4.4's table).
7. `docs/languages/minizinc.md` §4.1 (the division conventions the *integer* languages need).
8. `docs/languages/sygus-if.md` §4.1 (the second filter failing on question shape, against
   §4.1's failing on method).
9. `docs/languages/flatzinc.md` §4.3, `docs/languages/lp.md` §4.2 (the same
   "fresh variable without its defining constraint" shape as §4.3).
10. `docs/languages/qdimacs.md` §5, `docs/languages/aiger.md` §5 (the simplest-member
   sequencing rule §4.4 generalises).
11. `docs/languages/smtlib2.md` §4.1 (cluster F unblocks QF_BV there too).
12. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `include/somtparser/core/kind.h`.
