# BTOR2 — word-level hardware model checking

**Date**: 2026-08-25
**Status**: **implemented** (`languages/btor2/`), using option C of
`docs/design-transition-system.md` -- the system lives inside the frontend and the unrolling
is recorded as an `EncodingChoice` with a `BMC_DEPTH` bound.
**Scoping context**: `docs/languages-scoping.md` §3.1 clusters **D + F**, §3.2, §4.

<!-- proposed-hir: ExprKind::NEXT, ExprKind::ITE_EXPR -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

<!-- implicit-constraints:
  a state with an `init` line => that value holds at step 0 only; a state with NO init line is unconstrained at step 0 and must stay unconstrained, not defaulted to zero (§2.4, §4.3)
  a state with no `next` line => is treated as a primary input and takes a fresh nondeterministic value at every step; adding a frame equation removes valid traces (§2.4, §4.3)
  an `input` node => a fresh unconstrained value at EVERY step, so unrolling must introduce a new variable per step rather than reusing one (§4.2)
  every `constraint` line => an invariant assumed at every step of the finite witness through the bad frame; it is not required after an earlier witness merely because the configured bound is larger (§2.4, §4.2)
  a `bad` property => asks whether the state is REACHABLE; BMC finding no witness up to depth k proves nothing beyond k, which is what Bound::BMC_DEPTH records (§4.2)
  bit-vector width is part of every operation => a width mismatch is a malformed file, and an operation's result width is fixed by its sort line rather than inferred (§2.3)
  an init expression => refers only to earlier nodes, precedes its state id, and contains no input dependency; otherwise it is not a legal initial-state function (§2.1, §2.4)
  an array state initialized by a bit-vector constant => denotes the constant array whose every element has that value, not an array/bit-vector equality (§2.4)
  an output => is a projected observation at each frame and is never reinterpreted as a bad property (§2.4)
-->

**Headline result of the audit in §4**: the safety fragment now covers all official constant,
bit-vector, array, state, constraint, bad and output constructs. The frontend unrolls directly
to typed HIR and records `underApprox(BMC_DEPTH=k)`. Indexed rotations and overflow predicates
use explicit equivalent relations; liveness remains refused until a lasso encoding exists.

The second finding is a modelling trap stated directly by the BTOR2 paper (§4.3): a state
with no `next` is treated as a primary input, hence fresh at every step, and a state with no
`init` is unconstrained at step 0. Inventing either a frame equation or a zero initializer
removes legal source traces.

---

## 1. What the format is

BTOR2 is a word-level format for describing sequential circuits and their safety and
liveness properties, and for stating model-checking queries over them. It is the input of
the Hardware Model Checking Competition's word-level track, the format Yosys emits from
Verilog, and what `btormc` and Pono read.

Its predecessor BTOR was bit-vector only; BTOR2 adds arrays and the liveness constructs.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| A. Niemetz, M. Preiner, C. Wolf, A. Biere, *BTOR2, BtorMC and Boolector 3.0* (CAV 2018) | the format definition | <https://cs.stanford.edu/~preiner/publications/2018/NiemetzPreinerWolfBiere-CAV18.pdf> |
| `btor2tools` — reference parser, `btorsim` simulator | official implementation, checked 2026-08-25 | <https://github.com/hwmcc/btor2tools> |
| Hardware Model Checking Competition (HWMCC) | the corpus | — |

The repository fixtures are accepted by a locally built checkout of the official parser.
Competition archive counts and licences still need pinning before corpus-scale experiments.

### Corpus

HWMCC's word-level track archives, per edition. The competition supplies a corpus, reference
implementations and published results, so it passes `docs/languages-scoping.md` §7's first
filter.

The **second** filter (§6 there) needs care and is §4.2's subject: HWMCC asks whether a bad
state is reachable *at all*, and a bounded translation asks whether it is reachable *within
k steps*. Those are different questions, and the difference is exactly what
`Fidelity::underApprox` with `Bound::BMC_DEPTH` exists to record
(`include/somtparser/translation/fidelity.h:90`).

---

## 2. Semantics — what a file means

### 2.1 The line format

Every line is `<id> <name> <sort-id> [<arg-id> …] [<symbol>]`, ids increasing, referring
only backwards. It is SSA over a DAG — no blocks, no control flow, no reuse of an id.

```
1 sort bitvec 1
2 sort bitvec 8
3 constd 2 0
4 input 2 x
5 state 2 counter
6 init 2 5 3
7 constd 2 1
8 add 2 5 7
9 next 2 5 8
10 constd 2 200
11 eq 1 5 10
12 bad 11
```

Read: an 8-bit state `counter`, initialised to 0, incremented each step, with `counter = 200`
as the bad state.

### 2.2 Sorts

`sort bitvec <width>` and `sort array <index-sort-id> <element-sort-id>`. Every node carries
a sort id; the format is fully explicit, which makes a frontend's job easy and makes a width
mismatch a malformed file rather than something to infer.

### 2.3 Operators

The implemented safety inventory includes all official constants; unary arithmetic and
reductions; arithmetic, division/remainder, bitwise, shifts and variable rotations; signed
and unsigned comparisons and overflow predicates; concat/slice/extensions; `ite`; array
equality, `read`, `write`, array-valued `ite`, and constant array initialization.

Every one of these has an `NT_BV_*` counterpart in the engine — that is the point of §4.1.

**A division note**, since this batch keeps meeting one: BTOR2's `udiv`/`sdiv`/`urem`/`srem`
are the *bit-vector* operations, which SMT-LIB's `FixedSizeBitVectors` theory defines
identically (`bvudiv`, `bvsdiv`, `bvurem`, `bvsrem`), including the total behaviour at zero
— `bvudiv x 0` is all-ones. This is the one language in the batch where the division
convention needs **no** decision, because both sides are the same theory. Contrast
`minizinc.md` §4.1, where the same-looking operator meant three different things.

### 2.4 The sequential constructs

| Line | Meaning |
|---|---|
| `input` | an unconstrained value, **fresh at every step** |
| `state` | a state component; only an explicit `next` defines its transition |
| `init <sort> <state> <value>` | the state's value at step 0; expression has no input dependency |
| `next <sort> <state> <value>` | the state's value at step *i+1*, as a function of step *i* |
| `constraint <node>` | an invariant holding at every step of the finite witness |
| `bad <node>` | a safety property: is this reachable? |
| `fair <node>`, `justice <n> <node…>` | liveness (§4.5) |
| `output <node>` | derived observation, projected at every unrolled frame |

The missing lines denote nondeterminism: a `state` with no `init` is unconstrained at step
0, and a `state` with no `next` is fresh at every later step. §4.3.

### 2.5 What a solution is

For a `bad` property: a **witness trace** — a sequence of input values reaching the bad
state — or a proof that none exists. `btorsim` replays a witness, which makes model-level
differential validation available, unlike QBF (`qdimacs.md` §2.4).

---

## 3. Construct → HIR mapping

The current implementation performs the bounded transformation inside the frontend. The
result is an ordinary `ConstraintModel`; its transition-system origin, decision mapping and
bound are carried by the translation contract and report.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| `sort bitvec n` | `Sort{BITVEC, width = n}` | **`SortKind::BITVEC`** | `exact()` |
| `sort array i e` | `Sort{ARRAY, …}` | **`SortKind::ARRAY`** | `exact()` |
| `const`/`constd`/`consth`/`zero`/`one`/`ones` | a bit-vector literal | **`ExprKind::LIT_BITVEC`** | `exact()` |
| direct bit-vector operators | corresponding typed HIR operator | existing bit-vector HIR | `exact()` |
| `inc`/`dec`, reductions, variable `rol`/`ror`, overflow | exact HIR relations over primitive bit-vector operations | none | `exact()` |
| `ite` | `Op::ITE` over bit-vectors or arrays | existing | `exact()` |
| `read` / `write` | array select/store | `SortKind::ARRAY` | `exact()` |
| `input` | fresh declaration at every frame | none | `exact()` within the bound |
| `state` | one declaration per frame | none | `exact()` within the bound |
| `init` | step-0 equation; constant-array constructor when specified | none | `exact()` |
| `next` | equation `s@(i+1) = e@i` | none | `exact()` |
| **a state with no `next`** | no transition equation; a fresh state value at each step (§4.3) | none | `exact()` |
| **a state with no `init`** | **nothing** — do not default (§4.3) | — | `exact()` |
| `constraint` | assertion at every frame | none | `exact()` |
| `bad` | member of the reachability disjunction over frames | none | **§4.2** |
| `fair` / `justice` | refused before lowering | lasso encoding | — |
| `output` | per-frame declaration plus defining equality, included in beta | none | `exact()` |

---

## 4. Semantic gaps and encoding choices

### 4.1 Bit-vector and array semantic adapters

HIR now has width-parameterised bit-vectors and total extensional arrays. Direct operators map
one-to-one. `inc`/`dec` lower to modular add/subtract; reductions return a one-bit vector;
variable rotations reduce the amount modulo the word width before combining shifts; overflow
predicates use wraparound and signed-sign relations. Exhaustive tests cover every pair of
3-bit operands, and an official-parser-accepted aggregate is checked by Z3.

Two choices remain load-bearing:

1. **Is the width part of the sort or of the operation?** BTOR2 says the sort. SMT-LIB says
   the sort. Follow both — a width-parameterised `Sort` — rather than putting widths on
   operators, or every operator gains a field that is redundant for the other sorts.
2. **What is the HIR's array?** BTOR2's array is SMT-LIB's: index sort, element sort,
   select/store. Cluster A's array wants *index sets* and multi-dimensional indexing.
   **Answered 2026-08-12: they are one type** — SMT-LIB's. An index set is not part of the
   sort but a constraint on the indices, expressible once quantifiers are available, so
   cluster A's requirement is met by the same array plus ordinary assertions. See
   `docs/hir-design-decisions-2026-08-12.md` §3.1.

### 4.2 BMC is an under-approximation, and its Bound already exists

A transition system with a `bad` property asks: is the bad state reachable in *any* number
of steps? SMT answers a bounded version: is it reachable in at most *k*?

```
⋁_{j≤k} [init(s₀) ∧ ⋀_{i<j} trans(sᵢ,sᵢ₊₁) ∧ ⋀_{i≤j} invariants(sᵢ) ∧ bad(sⱼ)]
```

| Answer | Means | Fidelity |
|---|---|---|
| SAT | a real counterexample at depth ≤ k — **sound**, the trace is genuine | — |
| UNSAT | no counterexample **within k**; says nothing beyond | `underApprox` with `Bound::BMC_DEPTH = k` |

`Fidelity::underApprox(Bound)` and `Bound::BMC_DEPTH` both exist already
(`include/somtparser/translation/fidelity.h:90`, `:134`), so this needs no lattice work — cluster D's
pass records the depth and the report carries it.

The prefix form is load-bearing. Requiring invariants through the configured frame `k`
can erase a valid shorter witness that reaches `bad` at frame `j<k` but cannot be extended
under the invariant. The implementation constructs one invariant prefix per candidate frame.

**The reporting consequence is the important part.** An experiment that counts a bounded
UNSAT as "solved" is comparing against HWMCC solvers that proved *unbounded* safety, usually
by k-induction or IC3/PDR. That is the `docs/languages-scoping.md` §6 second filter: the
corpus is usable, the SAT results are directly comparable (a counterexample is a
counterexample), and the UNSAT results are **not** a baseline unless the translation also
does induction.

Two ways to make the UNSAT side meaningful, both real options rather than hand-waving:

- **k-induction**: add the induction step as a second query. Still not complete, but the
  answer "safe" is then unbounded when the induction succeeds — a genuinely different and
  stronger claim, and one that fits the existing `EncodingChoice` mechanism as a distinct
  strategy with a distinct `Fidelity`.
- **Report the two halves separately**: reachability-found (comparable) and
  bounded-not-found (not comparable). Cheap, honest, and it makes the limitation visible in
  the results table rather than in a footnote.

### 4.3 Missing `init` and `next` mean nondeterminism

**A `state` with no `next` line is treated as a primary input.** This is explicit in the
BTOR2 CAV'18 format paper: its value is fresh at every step. Adding `NEXT(s) = s` is not a
conservative frame rule; it removes legal behaviours and may hide a real counterexample.
**Direction: incomplete.**

**A `state` with no `init` line is unconstrained at step 0.** The tempting default is zero —
because hardware registers usually reset to zero, and because a concrete value makes the
unrolling smaller. Adding `s₀ = 0` **removes** initial states, so a bad state reachable only
from a non-zero start becomes unreachable. **Direction: incomplete.** It reports "safe" for
an unsafe circuit.

Both absent functions leave values unconstrained. The rule is: **add no equation for a
source function that was not declared.**

Both belong in `instances/ok/` fixtures whose answer changes if the rule is wrong: one bad
state is available only from a non-zero initial value, and another only after a state with
no `next` takes a fresh value.

### 4.4 Arrays and initialization

BTOR2 arrays model memories. Unrolling a system with an array state to depth *k* copies the
array *k* times, and SMT array reasoning is already the expensive part.

| Encoding | Fidelity | Note |
|---|---|---|
| SMT array theory, one array term per step | `exact()` | the direct route; needs `SortKind::ARRAY` |
| Bit-blast the array to individual cells | `exact()` if the index width is small | size is 2^(index width) — usable for small memories only |
| Bound the addressable range | `underApprox` with `Bound::DOMAIN_CUT` | a real option for large memories, and the `Bound` exists |

Note the third row is a *different* bound from the BMC depth, and a translation may carry
both. `Fidelity::meet` unions bounds and now sorts them canonically, so a report with two
bounds is stable across pass order (`test/translation/test_uir_fidelity.cpp`).

The current adapter uses only the first row. A bit-vector constant in an array `init` is
translated with SMT-LIB's constant-array constructor. Emitting `array = bitvector` is not an
approximation; it is simply ill-typed.

### 4.5 Liveness is a different problem, not a harder one

`justice` and `fair` express liveness: "something good happens infinitely often". A
bounded unrolling cannot express that at all — no finite prefix witnesses an infinite
behaviour.

The standard technique is a **lasso**: search for a finite trace with a loop back to a
previously seen state, with the justice condition satisfied inside the loop. That is a
genuinely different encoding from safety BMC, with its own soundness argument.

| Option | Fidelity | Recommendation |
|---|---|---|
| Lasso-shaped bounded liveness | `underApprox` on depth | correct, and a real piece of work |
| Treat `justice` as a `bad` property | **wrong** — answers a different question | never |
| Refuse with `E_UNSUPPORTED_CONSTRUCT` | honest | **the right first step** |

`pddl.md` §5's `Property` struct already separates `formula` (safety/reachability) from
`justice` and `fairness` lists, so the HIR shape is ready for the distinction before the
encoding exists — which is what lets a frontend refuse liveness *specifically* rather than
refusing the file.

---

## 5. New HIR surface this format forces

| Surface | Cluster | Also needed by |
|---|---|---|
| **`SortKind::BITVEC`**, width-parameterised, plus the bit-vector operator set and `ExprKind::LIT_BITVEC` | **F** | CryptoLine; unblocks QF_BV for `smtlib2.md` |
| **`SortKind::ARRAY`** in SMT-LIB's sense (§4.1) | F-adjacent | AIGER (no), VMT-LIB, MoXI, SMT-LIB 2 |
| **`TransitionSystem`** and `Property` | **D** | AIGER, VMT-LIB, MoXI, PDDL — specified in `pddl.md` §5 |
| **`ExprKind::NEXT`** | D | the whole of cluster D |
| a BMC unrolling pass recording `Bound::BMC_DEPTH` | D | the whole of cluster D |
| `Op::ITE` | — | FlatZinc, XCSP3, LP, MPS, MiniZinc |

**Not needed**: quantifiers, uninterpreted functions, objectives, comprehensions, real
literals. BTOR2 is deep rather than broad — two clusters, both structural.

---

## 6. Fidelity summary

**Exact — the combinational half.** Every sort, every constant form, every bit-vector and
array operator, `ite`, and the transition relation itself. BTOR2's operators are SMT-LIB's
bit-vector operators, including the total-at-zero division behaviour, so there is no
convention to choose (§2.3).

**`underApprox` — the sequential half.** BMC to depth *k* carries
`Bound::BMC_DEPTH` (§4.2). A bounded UNSAT is not a proof of safety and must not be reported
as one.

**Optional future `underApprox` — large arrays**: a domain cut would require an additional
explicit `Bound::DOMAIN_CUT`; the current implementation does not apply one (§4.4).

**Refused, not approximated**: `justice` and `fair` until a lasso encoding exists (§4.5).

**Ways to make it wrong by mistake**:

- Adding `NEXT(s) = s` for a state with no `next` line (§4.3). **Incomplete: removes
  nondeterministic source traces.**
- Defaulting a state with no `init` line to zero (§4.3). **Incomplete: reports safe for an
  unsafe circuit.**
- Reusing one variable for an `input` across steps instead of a fresh one per step (§4.2).
  Constrains the environment to behave identically at every step.
- Counting a bounded UNSAT as "solved" against solvers that proved unbounded safety (§4.2).
  **Not a fidelity error — a reporting one, and no `Fidelity` value catches it.**
- Encoding `justice` as `bad` (§4.5).
- Treating a bit-vector constant array initializer as an array/bit-vector equality (§4.4).
- Accepting forward references, wrong declared result sorts, or input-dependent init
  expressions. These are malformed source programs, not target-side nondeterminism.
- Dropping `output` from beta, or treating it as `bad`; observations and properties are
  different components of the source institution.

---

## 7. References

**Format**

1. [A. Niemetz, M. Preiner, C. Wolf, A. Biere, *BTOR2, BtorMC and Boolector 3.0*](https://cs.stanford.edu/~preiner/publications/2018/NiemetzPreinerWolfBiere-CAV18.pdf), CAV 2018.
2. [`btor2tools`](https://github.com/hwmcc/btor2tools) reference parser and `btorsim`.
3. Yosys, which emits BTOR2 from Verilog. **Not re-confirmed.**

**Competition and corpus**

4. Hardware Model Checking Competition, word-level track. Per-edition archives; instance
   counts and licence terms **not re-confirmed**.

**This project**

5. `docs/languages-scoping.md` §3.1 (clusters D and F), §3.2, §4 (Plan 2), §6 (the second
   filter §4.2 applies), §7 (the competition audit).
6. `docs/languages/pddl.md` §5 (the `TransitionSystem` and `Property` shape this document
   maps onto rather than re-specifying). PDDL's frame rule does not apply to an omitted
   BTOR2 `next`; §4.3 records that language-specific difference.
7. `docs/languages/aiger.md` (the bit-level sibling), `docs/languages/vmt-lib.md`,
   `docs/languages/moxi.md` (the other cluster-D members).
8. `docs/languages/smtlib2.md` §4.1 (the same bit-vector gap, measured from the target
   side — cluster F unblocks both).
9. `docs/languages/essence-prime.md` §4.4 (cluster A's different array requirement, §4.1).
10. `docs/languages/minizinc.md` §4.1 (the division-convention problem BTOR2 does *not*
    have, §2.3).
11. `docs/languages/qdimacs.md` §2.4 (verdict-only comparison, which BTOR2 improves on via
    `btorsim`, §2.5).
12. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `include/somtparser/core/kind.h`, `test/translation/test_uir_fidelity.cpp`.
