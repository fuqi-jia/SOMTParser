# Boogie — an intermediate verification language

**Date**: 2026-08-25
**Status**: **implemented for a structured verification core**
(`languages/boogie/`): declarations, axioms/functions, procedures, contracts —
**calls included, as the two-sided contract of §2.3 plus the caller frame
(2026-09-19)** — assignments, havoc, assertions/assumptions, invariant-based
`while` loops, and — **2026-09-20** — **branching** (`if`/`else if`/`else`,
`if (*)`) as This is Boogie 2 §9.7's two-edge join and `return` with the
ensures obligatorified at every exit point, plus **general control flow**:
labels, `goto` (incl. goto loops under the reference's implicit-true-invariant
cut) and `break`. Refused by name: a `goto` into a structured statement's body
or looping across a `while` boundary, multi-index maps, `async call`, `where`
clauses and procedure type parameters. **2026-10-07:** separate `implementation`
bodies inherit their procedure's contracts, matching parameter types and positions
while allowing different names and declaration order. Multiple bodies are checked
independently in both the direct VC and `chc=1` routes. See the focused
validation record.
**Scoping context**: `docs/languages-scoping.md` §3.1 clusters **G + H**, §3.2, §4.

### Explicit frame inference (2026-10-10)

For generated programs that omit body effects from their `modifies` clauses,
the Python translation API accepts `options={"infer_modifies": "1"}`. The
frontend collects mutable-global assignments, `havoc` targets, map-update bases,
and call-result targets, then computes the transitive call-graph fixed point.
Separate implementations of a procedure contribute to the same effect union.
Declared checked frames remain included, even if a body writes fewer globals;
shrinking a declared frame would strengthen the caller's assumptions incorrectly.

```python
result = somtparser.translate(
    source=program, language="boogie", options={"infer_modifies": "1"}
)
```

The inference applies to both the direct VC route and `chc=1`. Reports record
the declared frame, direct writes, callees, and resulting checked frame under
`call-graph-modifies-fixed-point`. This is an explicit source configuration:
the default still checks the written `modifies` clauses. It does not introduce
concurrent semantics for `async call` or make writes to constants and incoming
formals legal. Procedure-entry aliases for `old` expressions are fresh for each
implementation, preserving independent entry states across procedures.

Validation is in `test/python/test_boogie_infer_modifies.py` and
`test/python/test_boogie_old_entry_aliases.py`; it includes recursive call graphs,
multiple implementations, both VC polarities, and unchanged-global counterexamples.

<!-- proposed-hir: SortKind::MAP, Op::IFF, Bound::LOOP_UNROLL -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

<!-- implicit-constraints:
  a procedure's `requires` clauses => assumed at entry to its body AND asserted at every call site; a translation that does only one of the two either verifies a procedure nobody can call or lets a caller violate its contract (§2.3, §4.2)
  a procedure's `ensures` clauses => asserted at exit from its body AND assumed after every call site; the same two-sided obligation (§2.3, §4.2)
  a `modifies` clause => everything NOT listed is unchanged by the call, so a caller must be told the frame; omitting it lets a call change any global and is the frame problem again (§2.3, §4.2)
  `havoc x` => x becomes an arbitrary value of its type, so the translation must introduce a FRESH variable rather than dropping the statement (§2.2)
  a loop with an `invariant` => the invariant is assumed at the top of an arbitrary iteration, asserted on entry, and asserted at the end of the body; using it only as an assumption is unsound (§4.3)
  a loop WITHOUT an invariant => nothing is known after it, so the verification condition must havoc every variable the loop modifies rather than carrying facts across it (§4.3)
  an `axiom` => assumed globally, at every program point, and can make the whole verification vacuous if inconsistent; an inconsistency check is not optional (§4.4)
  a quantified axiom with a `:trigger` => the trigger controls instantiation and therefore completeness, not meaning; dropping it changes what the solver can prove but not what is true (§4.5)
  declarations are NOT ordered => a symbol may be used above its declaration, so a frontend that requires declare-before-use REJECTS A LEGAL PROGRAM rather than declining a construct (§2.1)
  a `const` is never assigned => it has exactly one SSA version and must not be versioned; `unique` is a distinctness constraint over ALL uniques of its type, and half of one admits models the source excludes (§2.1)
  an incoming formal => it is immutable, while locals, outgoing formals, and mutable globals are assignable; accepting an assignment to an input enlarges the source transition relation (§2.2)
  an assignment or `havoc` of a mutable global => that global must occur in the enclosing procedure's `modifies` set (§2.3)
  an axiom or function body => it is stateless and cannot refer to mutable globals; doing so would give a single logical symbol a state-dependent meaning (§2.1)
  a parallel assignment target base => it occurs at most once; repeated scalar or map-base targets are ill-formed rather than sequential updates (§2.2)
  a `function` with a body => a declaration plus `forall x. f(x) = body`, not an inlining: both are exact and only the axiom form survives a recursive definition, which Boogie allows (§2.1)
  a `uses { axiom ... }` block => its axioms are included when the symbol is used, so including them unconditionally cannot change the answer and dropping them can (§2.1)
  a parallel assignment `x, y := e, f` => every right-hand side is read BEFORE any target is updated, which is what makes `x, y := y, x` a swap (§2.2)
-->

**Headline result of the audit in §4**: Boogie is the batch's only language where **the
translation is a program semantics, not a syntax mapping** — and that puts its correctness
somewhere the fidelity lattice cannot see (§4.1). Every other document here can say "this
construct maps to that HIR node, exactly or with a recorded loss". Boogie's frontend is a
**verification-condition generator**: it computes a formula whose validity means the program
is correct, and *soundness lives in that computation*. A weakest-precondition bug produces a
perfectly well-formed SMT script for a formula that is not the program's VC. `Fidelity` will
say `exact()`, because nothing was approximated — the wrong thing was computed exactly.

The second finding is a route worth taking seriously before building anything: **Boogie's
natural target is CHC, not SMT** (§4.6). CHCs are the standard IR for exactly this
translation, `chc-comp.md`'s cluster E already specifies the shape, and going
Boogie → CHC → SMT means the VC generator is checkable against CHC-COMP solvers rather than
only against Boogie itself.

---

## 1. What the format is

Boogie is an intermediate verification language: a small imperative language with
contracts, designed as a compilation target for verifiers of real languages. Dafny, Corral,
VCC and others translate to it; Boogie translates to SMT and reports which assertions cannot
be proved.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| Boogie Language Reference | current online reference, checked 2026-08-25 | <https://boogie-docs.readthedocs.io/en/latest/LangRef.html> |
| The Boogie implementation | `boogie-org/boogie` main source, checked 2026-08-25 | <https://github.com/boogie-org/boogie> |

### Corpus — and it is a different kind of corpus

**Boogie has no competition.** That is the first thing to plan around, and it is a sharper
version of Essence′'s problem (`essence-prime.md` §1): there is no ranked archive, no
published baseline, and — unlike Essence′ — the instances that exist are mostly **generated**
by Dafny and other frontends rather than written by hand.

| Property | Consequence |
|---|---|
| Generated, not curated | instance characteristics reflect the generator's idioms, not a designed benchmark distribution |
| No ranking | `docs/languages-scoping.md` §7's first filter fails: corpus yes, reference implementation yes, **published baseline no** |
| Boogie itself is the only reference | so Boogie is the oracle, exactly as Savile Row is for Essence′ (`essence-prime.md` §4.1) |

That last row is the productive framing again: Boogie emits SMT-LIB, so every Boogie program
yields two independent SMT scripts, and disagreement is a bug in one of them. It is the
second-cheapest differential test in the batch after Essence′'s.

---

## 2. Semantics — what a file means

### 2.1 Declarations

```boogie
type Ref;
const null: Ref;
function f(x: int): int;
axiom (forall x: int :: f(x) > x);
var heap: [Ref, Field]int;
```

Types are `bool`, `int`, `real`, `bv<n>`, user-declared type constructors, and **maps**
`[K1, K2]V`. Maps are the heap encoding and are Boogie's most-used non-trivial type.

**Declarations are not ordered.** A symbol may be used above its declaration, and Boogie's
own `Test/textbook/TuringFactorial.bpl` does exactly that — `Factorial(n)` in a
postcondition on line 9, `function Factorial(int): int` on line 31. A frontend that
requires declare-before-use therefore **rejects a legal program**, which is a different
class of wrong from declining a construct, and this one did until 2026-08-14. It now makes
two passes over the file: the first collects declarations, the second reads axioms and
procedure bodies.

A **`const`** is a global that is never assigned, so unlike a `var` it has exactly one SSA
version and must not be versioned. `unique` asserts that the marked constants are pairwise
distinct over *all* unique constants of a type, not per declaration. The frontend therefore
accumulates them across declarations and emits the complete `distinct` relation.

A **`function` with a body** becomes a declaration plus `forall x. f(x) = body` rather than
an inlining. Both are exact; the axiom form is chosen because it keeps the one symbol and
one defining equation the source wrote, and because it survives a *recursive* definition,
which Boogie allows and an inliner cannot terminate on.

A **`uses { axiom ... }`** block attaches axioms that Boogie includes only when the symbol
is used. That is a performance device: including them unconditionally cannot change the
answer, because an axiom about a symbol nothing references constrains nothing, while
dropping them can. So they are read — after the declaration pass, since a block may name a
function declared further down, which is again what TuringFactorial does.

### 2.2 Statements

`assume`, `assert`, `havoc`, assignment, `call`, `if`, `while`, `goto`/`label`, `break`,
`return`. The `goto` form makes the control-flow graph arbitrary, which matters for §4.1.

**Branching and exit points, implemented 2026-09-20.** `if (c) T else E` and `if (*)`
follow This is Boogie 2 §9.7's desugaring — each branch is checked under an assumption
of the guard (resp. a fresh Boolean), and at the join every variable the paths disagree
on takes an `ite` of the two versions; exact because the edges are exclusive by
construction. `return` obligatorifies the checked `ensures` at each exit point, and
unreachable code is parsed and type-checked but has no VC effect, matching the
reference's pruning of unreachable blocks. A `return` inside a loop body owes no
invariant preservation (the completion guard handles it).

**General control flow, same day.** Labels and `goto` (This is Boogie 2 §9.5) are the
edge-join generalisation: a syntactic pre-scan splits each statement list into
segments, classifies every goto (forward: an edge into the target's join; backward: a
loop header's back edge), and computes each cycle's assigned variables by reachability
on the segment graph. Joins with non-exclusive edge guards get fresh gate Booleans (the
passified-CFG discipline); an if's own branches are exclusive by construction and join
on the guard directly. A backward edge is *cut*: the reference verifies a goto loop at
its header with the header's *leading assert prefix as the invariant set* — asserted on
entry and at back edges, assumed at the head — and with an implicit `invariant true`
when there is none (`RemoveBackEdges.cs`), which here is the same havoc-and-continue as
a no-invariant `while`; the reference makes irreducible CFGs reducible by node splitting
rather than rejecting them (`Implementation::ConvertToReducible`;
`Test/irreduciblecfg/Canonical.bpl` verifies). `break` (plain or labeled) is a forward
edge to the enclosing construct's join. Refused by name: a `goto` into a structured
statement's body, and a goto loop crossing a `while` boundary (the two loop encodings
do not compose).

A **parallel assignment** `x, y := e, f` reads every right-hand side before updating any
target. That is what makes `x, y := y, x` a swap: versioning the targets one at a time
would let the second read the value the first had just written.

`havoc x` sets `x` to an arbitrary value of its type. It is the language's non-determinism
primitive and translating it as a no-op is a soundness error.

### 2.3 Procedures and contracts

```boogie
procedure Inc(x: int) returns (y: int)
  requires x >= 0;
  ensures  y == x + 1;
  modifies globalCounter;
{ y := x + 1; globalCounter := globalCounter + 1; }
```

Each clause carries a **two-sided** obligation, which is the implicit-constraints block's
first three entries and §4.2's subject:

| Clause | At the body | At each call site |
|---|---|---|
| `requires` | **assumed** | **asserted** |
| `ensures` | **asserted** | **assumed** |
| `modifies` | bounds what the body may change | tells the caller what is *unchanged* |

**Implemented 2026-09-19 for calls** (`callStatement` in
`languages/boogie/src/boogie.cpp`), following This is Boogie 2 §8.2/§9.9/§9.10:
the caller asserts each *checked* `requires` as its own refutation branch,
havocs the callee's *checked* `modifies` globals and the out-targets, and
assumes every `ensures` with `old()` resolved to the call-entry state;
`free requires` are ignored by the caller, `free ensures` are not asserted at
the body, `free call` skips the assertion, and `call forall` over a lemma
procedure becomes `assume (forall wildcards :: Pre ==> Post)`. The callee's
whole `modifies` set must lie inside the caller's, the reference
implementation's CheckAssignments rule. Two spec-readings this surfaced:
`old()` is the *identity* on non-globals (This is Boogie 2 §4.3 — only a
mutable global gets an entry alias), and Boogie permits a local to shadow a
global while this frontend's name-keyed SSA cannot — shadowing is a named
refusal rather than a silent mis-versioning.

### 2.4 What a solution is

Boogie reports, per assertion, whether it is provable. The SMT query is the *negation* of
the verification condition: `unsat` means the VC is valid, i.e. **the program verifies**.

That is a polarity inversion of the same family as `tptp.md` §4.1's conjecture negation, and
the fourth in this batch. It also means a Boogie arm's "solved" is `unsat`, which is the
opposite of most of the others.

### 2.5 Institutional translation contract

The source Institution is

\[
\mathcal I_{B}=(\mathbf{Sign}_{B},\operatorname{Sen}_{B},
\operatorname{Exec}_{B},\models_{B}),
\]

where the signature contains types, constants, mutable globals, functions and procedure
interfaces; sentences are global axioms plus procedure proof obligations; models are typed
executions; and an execution satisfies a program exactly when every reached assertion,
postcondition, loop-entry invariant and loop-preservation obligation holds.

For the implemented adapter `T=(Phi,A,alpha,beta,h)`:

- `Phi` maps source types and functions to HIR/SMT symbols and each mutable program point to
  a fresh SSA symbol.
- `A` contains global axioms, cross-declaration `unique` relations, typing/immutability rules,
  and `modifies` write permissions.
- `alpha` maps every source obligation `o_i` with its own path prefix `p_i` to the refutation
  branch `p_i AND NOT(o_i)`; all branches are disjoined.
- `beta` decodes a satisfying SSA model into a source-level counterexample trace and removes
  auxiliary versions. There is no optimization objective, so `h` is the empty identity.

Thus target `SAT` means a source counterexample exists, while target `UNSAT` verifies all
represented obligations. Soundness requires every decoded `SAT` model to be a legal source
execution violating its reported obligation; completeness requires every represented source
counterexample to extend to an SSA model. Loops are exact relative to checked invariants and
use no unrolling bound. Separate implementations use their declaration's checked/free
contracts and modifies permissions, with positional substitution for renamed formals.
Constructs lacking an exact `alpha` or `beta` are rejected rather than approximated.

---

## 3. Construct → HIR mapping

There is no construct-by-construct table for this language, and saying so is the point.

The frontend's product is not a translation of the program text; it is the **verification
condition** computed from it. What maps onto the HIR is the *formula*, and the formula's
vocabulary is:

| Formula element | HIR representation | New surface |
|---|---|---|
| program variables at a program point | `VarDecl`s, one per SSA version | none |
| `function` symbols | `ExprKind::APPLY` | cluster G |
| user `type`s | `SortKind::UNINTERPRETED` | cluster G |
| maps | select/store over a map sort | `SortKind::MAP` (§4.4) |
| `axiom`s | `Constraint`s, asserted globally | cluster C for quantified ones |
| quantifiers in contracts and axioms | `ExprKind::FORALL`/`EXISTS` | cluster C |
| `int` arithmetic | today's `Hir::Op` set | `Op::DIV_TRUNC`/`MOD_TRUNC` (§4.5) |
| `real` arithmetic | `ExprKind::LIT_REAL` (landed 2026-08-12) | none |
| `bv<n>` | — | cluster F |
| the VC itself | one `Constraint`, negated (§2.4) | none |

So Boogie's HIR requirements are **clusters C, G and F plus maps** — and the work that is
specific to Boogie is cluster **H**, which `docs/languages-scoping.md` §3.1 correctly
describes as "not a HIR struct addition — a frontend-level symbolic-execution /
weakest-precondition pass".

---

## 4. Semantic gaps and encoding choices

### 4.1 Soundness lives where `Fidelity` cannot see it

This is the finding.

For every other language in this batch, a translation bug shows up as a construct mapped
wrongly, and the fidelity lattice is the vocabulary for describing what a mapping preserves.
For Boogie the frontend *computes* a formula, and the question "is this formula the
program's VC?" has no `Fidelity` value at all:

| Bug | Symptom | What `Fidelity` says |
|---|---|---|
| a WP rule applied wrongly | a well-formed script for the wrong formula | `exact()` |
| a `modifies` frame omitted | the caller believes a global changed when it did not, or vice versa | `exact()` |
| a loop invariant used as an assumption but not asserted | unsound: unproved invariants accepted | `exact()` |
| a `havoc` dropped | unsound: non-determinism removed | `exact()` |

All four produce `exact()` because nothing was approximated. The lattice describes the
*relation between the HIR model and the SMT script*, and by the time the HIR exists the VC
has already been computed.

**What to do about it**, since "be careful" is not a mechanism:

- **The VC generator needs its own tests, not fidelity tests.** Per-rule tests
  (a program that verifies iff the rule is right) and, better, differential tests against
  Boogie's own SMT output (§1).
- **`Fidelity` should not be stretched to cover it.** A tempting move is to invent a
  `sound = false` for "the VC might be wrong", which would be a lie about a different thing —
  the lattice's `sound` means the *translated* problem's SAT implies the original's, which is
  a statement about a translation that is assumed correct.
- **Record the VC generation strategy in provenance.** Which WP variant, which loop
  treatment, which axiom set. Two Boogie arms with different strategies are different
  experiments.

This is the clearest case in the batch of `docs/languages-scoping.md` §6's second filter
being about *the pipeline*, not just about the language: the question is preserved, and the
thing that can silently go wrong is not in the lattice's domain.

### 4.2 Contracts are two-sided, and one side is easy to forget

§2.3's table. The failure modes:

| Half done | Consequence |
|---|---|
| `requires` assumed at the body, not asserted at calls | callers may violate preconditions freely — **unsound** |
| `requires` asserted at calls, not assumed at the body | the body must prove itself with no assumptions — **incomplete**, and very visibly so |
| `ensures` asserted at the body, not assumed at calls | callers learn nothing from a call — **incomplete** |
| `ensures` assumed at calls, not asserted at the body | the procedure never has to establish its contract — **unsound** |
| `modifies` ignored at calls | the caller's knowledge of unmodified globals is lost — **incomplete**; or if the caller assumes everything unchanged, **unsound** |

The unsound rows are the dangerous ones because they make verification *succeed*. A test
suite of programs that should fail to verify is therefore the right instrument, and it is the
`docs/known-defects-2026-08-11.md` §4 lesson in its natural habitat: a suite of programs that
all verify tests nothing about soundness.

That suite exists: `test/python/test_boogie_verdicts.py` runs every corpus program
through z3 and asserts the verdict, with half the corpus designed to *fail* —
a caller violating `requires`, a callee breaking `ensures`, a caller relying on
a havoc'd global (2026-09-19).

The `modifies` row is the frame problem again — `pddl.md`'s implicit-constraints block and
`btor2.md` §4.3 are the same idea in two other guises. Three of twenty-two languages have it;
it is the batch's most recurrent implicit constraint.

### 4.3 Loops: the choice, and its bound

A loop is where a VC generator must decide something.

| Strategy | Question answered | Fidelity | Note |
|---|---|---|---|
| **Trust the `invariant`** | is the program correct, *given* the invariant holds | `exact()` **for the VC**, and the invariant is verified as part of it (assert on entry, assume at top, assert at end) | Boogie's own default; complete relative to the annotation |
| **Unroll *k* times** | is the program correct on executions with ≤ *k* iterations | `underApprox` with a loop bound | needs a `Bound::Kind`; none of the four declared fits (§4.5) |
| Havoc modified variables, no invariant | is it correct with no loop knowledge | `exact()` but almost always unprovable | the honest default when no invariant is given |

The second row is where a `Bound` is needed and where the declared set falls short: `BMC_DEPTH`
is close in spirit but means transition-system steps
(`btor2.md` §4.2), and reusing it would put two different quantities in one bucket. This is
the third undeclared-bound finding in the batch, after `sygus-if.md` §4.3's
`GRAMMAR_RESTRICTION` and `syntcomp.md` §4.2's strategy size — and unlike those two, this one
has no reserved name in the design spec at all.

**Resolved 2026-08-17: the first row.** The user chose the invariant strategy, and it is
implemented — the invariant is an obligation on entry, preserved across the body, and the
loop's targets are havoc'd so the continuation is reasoned about from an arbitrary exited
iteration rather than from the entry state. `exact()`, and **no `Bound` is needed**, because
the invariant is *checked* rather than trusted. The undeclared-`Bound::Kind` question above
therefore stays open but is no longer blocking: it only arises if the unrolling row is ever
built as a second, selectable strategy.

Two things about the encoding are worth stating, because a single-query VC gets both wrong
by default and neither failure is visible in the output.

**The preservation check and the continuation are DIFFERENT PATHS**, and a conjunction
cannot hold two paths. Preservation is checked where the guard is true, the continuation
reasoned about where it is false; assume both of one state and the script is unsatisfiable —
which this encoding reads as *verified*. `i := 0; while (i < 10) invariant i <= 5; { i := i
+ 1; }` then proves, because `i <= 5` and `i >= 10` cannot both hold. So the loop uses two
havoc'd states, preservation is one self-contained implication carrying its own assumptions,
and the exit state's assumptions guard what *follows* the loop instead of constraining
everything.

**The havoc is what makes the continuation honest.** Without it, the code after the loop is
verified against the state before it ran — the classic unsound loop encoding. A loop with no
invariant at all degenerates to exactly the third row of this table, which is why
`instances/ok/loop_no_invariant.bpl` translates and is still sound.

### 4.4 Axioms can make everything vacuous, and maps are the heap

**Axioms** are assumed globally. An inconsistent axiom set makes every VC trivially valid —
the program "verifies" because `false` implies everything. This is not hypothetical: axiom
sets generated by front-ends like Dafny are large, and inconsistency is a known failure mode
of the technique.

A Boogie arm must therefore run a **consistency check** — is the axiom set alone
satisfiable? — and report an instance whose axioms are inconsistent as *invalid*, not as
verified. Skipping it means an arm whose success rate is partly measuring vacuous proofs.
This is an implicit constraint of the format (it is in the block above) and one with no
counterpart elsewhere in the batch.

**Maps** are Boogie's heap: `[Ref, Field]int` with select/store semantics. They map onto
SMT-LIB arrays cleanly, and the HIR's array question (`btor2.md` §4.1, `essence-prime.md`
§4.4) gains a third requirement here — multi-dimensional keys. That is one more reason the
"is cluster A's array the same type as cluster F's?" question should be settled before either
lands.

### 4.5 Arithmetic: the division convention, a fifth time

Boogie has integer `div` and `mod`. As with MiniZinc, FlatZinc, XCSP3 and Essence′, **the
convention must be read from the language description rather than assumed**, and
`minizinc.md` §4.1 has the three candidates, the failure mode and the recommendation to name
the convention in the HIR operator.

Boogie is the **fifth** language in the batch to reach this. At five out of twenty-two, the
per-frontend correction is clearly the wrong shape and `Op::DIV_TRUNC`/`Op::DIV_EUCLID`/
`Op::DIV_FLOOR` — the naming TPTP already uses for its own operators (`tptp.md` §2.5) — is
clearly the right one.

**Triggers** (`:trigger` annotations on quantified axioms) control instantiation. They affect
what the solver can prove, not what is true, so dropping them is *complete-preserving and
performance-destroying* — the translated problem has the same models and may become
unprovable in practice. That is a case where `Fidelity::exact()` is technically correct and
practically misleading, and it belongs in the report as a recorded choice rather than in the
lattice.

### 4.6 The better target is CHC

Boogie → SMT is one hop. Boogie → **CHC** → SMT is two, and the intermediate is the standard
IR for this exact translation: a procedure's contract and body become Horn clauses whose
solution is the program's inductive invariants (`chc-comp.md` §2.3).

| Route | Advantages | Costs |
|---|---|---|
| Boogie → SMT (VC generation) | one hop; matches what Boogie itself does | soundness is unverifiable outside the frontend (§4.1); loops need §4.3's choice up front |
| **Boogie → CHC → SMT** | cluster E's shape already exists in the plan; CHC-COMP solvers become an oracle for the *middle*; loop invariants are inferred rather than required; the CHC arm's tooling is reused | needs cluster E first; two translations to get right instead of one |

The second row's second point is the strong one. §4.1's problem is that a VC bug is
invisible; routing through CHC makes the intermediate a *checkable artefact* — the same CHCs
can be fed to Spacer or Eldarica, and disagreement with the SMT arm localises the bug.

**Landed 2026-09-20 as the D7 cross-check** (not as a replacement route): with the
`chc=1` parse option the frontend emits constrained Horn clauses from the *same* parse —
per-procedure summary relations whose exit clauses conjoin the ensures (the caller's
assumption is the relation's definition), per-loop-head relations (invariants are
inferred by the Horn solver; the source's checked invariants are error clauses, never
assumed), one relation per program point, and the `error!` query relation — and
`test/python/test_boogie_chc_crosscheck.py` asserts verdict agreement with the direct
VC route over the whole verdict corpus, plus CHC-COMP shape validation through the
`chc` frontend. Route-B-only limits, named: `call forall` with a wildcard (a
quantified lemma assumption is not a Horn clause), quantified axioms, function
definitions. Two emission details the cross-check caught live: a call must pass the
caller's *current* globals as the callee's entry positions, and a bodiless
procedure's summary must tie its entry and current binders; constants join the state
tuple because Spacer rejects free constants in rule bodies.

**Recommendation**: build cluster E for CHC-COMP first (`chc-comp.md` §5 notes it is
CHC-COMP's alone and nothing else amortises it), then reconsider Boogie as a cluster-E
producer rather than an SMT producer. That turns Boogie from the batch's least verifiable
frontend into one with a built-in oracle.

---

## 5. New HIR surface this format forces

| Surface | Cluster | Also needed by |
|---|---|---|
| a **VC generation pass** — not a HIR struct | **H** | CryptoLine (a much smaller instance of the same pattern) |
| `ExprKind::APPLY`, `SortKind::UNINTERPRETED` | **G** | TPTP |
| `ExprKind::FORALL`, `EXISTS`, `BOUND_VAR` | **C** | QDIMACS, TPTP, CHC-COMP, SYNTCOMP |
| **`SortKind::MAP`** with multi-dimensional keys | — | nothing else needs the multi-key form (§4.4) |
| `SortKind::BITVEC` | F | BTOR2, CryptoLine |
| `Op::DIV_TRUNC` / `DIV_EUCLID` / `DIV_FLOOR` | — | MiniZinc, FlatZinc, XCSP3, Essence′, CryptoLine, TPTP |
| ~~`ExprKind::LIT_REAL`~~ **landed 2026-08-12** | — | LP, MPS, MiniZinc |
| a **loop-unrolling `Bound::Kind`** | H | **undeclared, and unreserved** (§4.3) |

---

## 6. Fidelity summary

**Exact — the formula, once clusters C, G and F exist.** Program variables, functions, user
types, maps, axioms, quantified contracts, and the VC as a single negated constraint.

**`underApprox` — bounded loop unrolling** (§4.3), needing a `Bound::Kind` that does not
exist.

**Outside the lattice entirely — the VC's correctness** (§4.1). This is the document's
finding and no `Fidelity` value describes it.

**Recorded, not lattice-valued**: dropped triggers (§4.5), which preserve models and destroy
provability.

**Ways to make it wrong by mistake**:

- Any weakest-precondition rule applied wrongly (§4.1). **Reports `exact()`.**
- Doing one half of a `requires`/`ensures`/`modifies` obligation (§4.2). Two of the five
  half-done cases make verification *succeed*.
- Using a loop invariant as an assumption without asserting it (§4.3). **Unsound.**
- Dropping `havoc` (§2.2). **Unsound.**
- Not checking axiom-set consistency (§4.4). **Vacuous proofs counted as successes.**
- Assuming a `div`/`mod` convention (§4.5). Fifth occurrence.
- Reporting a Boogie arm's `unsat` as "unsolved" (§2.4). The polarity is inverted.
- Comparing against a baseline that does not exist (§1). There is no ranking.

---

## 7. References

**Language**

1. *Boogie Language Reference*. <https://boogie-docs.readthedocs.io/en/latest/LangRef.html>
   — grammar and static semantics checked 2026-08-25.
2. The Boogie implementation. <https://github.com/boogie-org/boogie> — resolver/typechecker
   mutability, assignment, `modifies`, and SMT integer arithmetic paths checked 2026-08-25.

**Corpus**

3. No competition; instances are generated by Dafny, Corral and similar. See §1 and
   `docs/languages-scoping.md` §7.

**This project**

4. `docs/languages-scoping.md` §3.1 (clusters G and H, and the "not a HIR struct addition"
   note §3 confirms), §3.2, §4 (Plan 2), §6 (the second filter, which §4.1 shows applies to
   the pipeline and not only the language), §7 (the competition audit).
5. `docs/languages/chc-comp.md` §2.3 and §5 (cluster E, and the route §4.6 recommends).
6. `docs/languages/tptp.md` §5 (cluster G), §2.5 (the division-operator naming §4.5 adopts).
7. `docs/languages/minizinc.md` §4.1 (the division conventions and the failure mode).
8. `docs/languages/btor2.md` §4.1 (the array-type question §4.4 adds a requirement to),
   §4.2 (`BMC_DEPTH`'s meaning, which §4.3 declines to overload), §4.3 (the frame problem).
9. `docs/languages/pddl.md` implicit-constraints block (the frame problem's first
   appearance).
10. `docs/languages/essence-prime.md` §1 and §4.1 (the same no-baseline position, and the
    oracle framing §1 reuses).
11. `docs/languages/sygus-if.md` §4.3, `docs/languages/syntcomp.md` §4.2 (the other two
    undeclared bounds).
12. `docs/known-defects-2026-08-11.md` §4 (why §4.2's fixtures must be programs that should
    *fail* to verify).
13. `include/somtparser/translation/fidelity.h`, `include/somtparser/hir/hir.h`.
