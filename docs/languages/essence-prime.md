# Essence′ — Savile Row's constraint modelling language

**Date**: 2026-08-12
**Status**: **implemented for the integer/matrix core** (`languages/essence/`).
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster A, §3.2 (cost **2.0×**), §4.
`docs/languages-scoping.md` §3.2 already records that "corpus is the weak point (§1.1), not
the implementation" — §1 below agrees and sharpens it.

<!-- proposed-hir: ExprKind::ARRAY_ACCESS, ExprKind::COMPREHENSION, Op::IFF -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

**Headline result of the audit in §4**: Essence′ is the **collision-risk language of the
batch**, and pretending otherwise would weaken the project rather than strengthen it.
Savile Row is a mature, published system that already reformulates Essence′ and already
targets SMT-LIB, choosing among alternative encodings automatically. A SOMTParser Essence′
frontend that stops at "we can also translate Essence′ to SMT" adds nothing. §4.1 states
what it does add, in terms that survive a reviewer who knows Savile Row: **per-instance
recorded fidelity**, **one IR across twenty-two languages**, and **the encoding choice as
data rather than as a decision made and forgotten**. Those are different contributions from
"better encodings", and claiming the latter against Savile Row would not hold.

The second finding is technical and cheerful: Essence′'s quantifiers are **bounded by
construction** (§4.2), so they expand rather than needing cluster C's quantifier surface.
Essence′ looks like it should be a quantifier language and is not.


<!-- implicit-constraints:
  a sparse domain `int(1, 3, 5)` => a membership constraint, as XCSP3 (§2.2, §4.5)
  a matrix index expression => must be constrained to the declared index domain, which need not start at 1 (§4.4)
  forall/exists/sum over a domain => expanded against the substituted parameter, so the quantifier's range is a materialised conjunction rather than a bound variable (§4.2)
  a `where` clause on parameters => a validity condition on the .param file, checked and reported as E_TYPE rather than lowered as a constraint (§3)
-->
---

## 1. What the format is

Essence′ is the constraint modelling language read by **Savile Row**, a modelling assistant
that reformulates a model and emits input for a target solver (Minion, SAT via DIMACS,
SMT-LIB, MiniZinc). It sits one level below **Essence**, the abstract specification language
that **Conjure** refines into Essence′ by choosing concrete representations for abstract
types like sets, functions and partitions.

The three-level structure matters for scoping:

| Level | Language | Who lowers it | In this batch? |
|---|---|---|---|
| Abstract specification | Essence | Conjure → Essence′ | no |
| Concrete model | **Essence′** | Savile Row → solver input | **this document** |
| Solver input | DIMACS / SMT-LIB / MiniZinc / Minion | the solver | separately |

Reading Essence′ rather than Essence is the right choice — Essence would put Conjure's
refinement decisions inside the measurement, exactly the problem `flatzinc.md` §4.1
describes for FlatZinc — but it is the *same* problem one level down, and §4.1 is about
that.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| Savile Row manual, including the Essence′ language description | tracks the Savile Row release; **exact version not re-confirmed in this pass** | <https://savilerow.cs.st-andrews.ac.uk/> |
| Nightingale, Akgün, Gent, Jefferson, Miguel, Spracklen, *Automatically improving constraint models in Savile Row* | Artificial Intelligence, 2017 | — |

There is **no independent standard**: Essence′ is defined by Savile Row's implementation and
manual. That is a materially weaker basis than MiniZinc's specification chapter
(`minizinc.md` §1) or XCSP3's format paper (`xcsp3.md` §1), and it means a frontend's notion
of "correct" is "agrees with Savile Row", which makes Savile Row the oracle rather than a
competitor — a useful reframing for §4.1.

### Corpus — the weak point

Essence′ has **no competition of its own**. `docs/languages-scoping.md` §7's audit is the
right lens: a competition supplies a corpus, a reference implementation and a published
baseline, and Essence′ supplies only the second. Instances exist in the Savile Row and
CSPLib ecosystems, but there is no per-edition archive with a solver ranking to compare
against.

**Consequence for the experiment**, stated plainly so it is not discovered late: an Essence′
arm can report *whether* translation succeeded and *what* was lost, but it cannot report
"SMT versus the state of the art on this corpus", because there is no ranked state of the
art on a fixed corpus to name. That is a smaller claim than the other twenty-one languages
support. `docs/languages-scoping.md` §3.2 already flags this; it is repeated here because
it is the single most important fact about this language for planning purposes.

---

## 2. Semantics — what a file means

### 2.1 Structure

```
language ESSENCE' 1.0
$ a comment

given n : int(1..)              $ parameter, supplied by a .param file
letting RANGE be domain int(1..n)

find q : matrix indexed by [int(1..n)] of RANGE
find total : int(0..1000)

such that
    allDiff(q),
    forall i, j : int(1..n) . i < j -> |q[i] - q[j]| != j - i,
    total = sum i : int(1..n) . q[i]

minimising total
```

Items: `language`, `given`, `letting`, `where`, `find`, `such that`, and one of
`minimising` / `maximising` (optional). Parameters arrive in a separate `.param` file
containing `letting` assignments — the same two-file shape as MiniZinc's `.dzn`, and
subject to the same rule: `Language::acceptsDataFiles()` must be overridden or
`translate()` will refuse the pair outright rather than silently translate the model alone
(`include/somtparser/translation/language.h:105`, and the refusal at `src/translation/translate.cpp:376-388`).

### 2.2 Domains

`bool`, `int(1..5)`, `int(1, 3, 5)`, `int(1..n)` with `n` a parameter, and `matrix indexed
by [D1, D2] of D` for multi-dimensional matrices. Domains may be named with `letting`.

As in XCSP3 (`xcsp3.md` §2.2), an integer domain is **a set, not a pair of bounds**:
`int(1, 3, 5)` is not `int(1..5)`. The HIR's `VarDecl` carries exactly `lower_bound` and
`upper_bound` (`include/somtparser/hir/hir.h`), so a sparse domain becomes an ordinary
membership constraint. Reading it as a range is unsound in the direction that admits extra
solutions.

### 2.3 Expressions

Arithmetic `+ - * / %`, `|x|` absolute value, comparison, Boolean `/\ \/ ! -> <->`,
matrix indexing `q[i]`, quantified expressions `forall`/`exists`/`sum` over a domain,
comprehensions `[ e | i : D, cond ]`, and a global-constraint library (`allDiff`, `gcc`,
`table`, `atmost`, `atleast`, `alldifferent_except`, …).

### 2.4 What a solution is

An assignment to every `find` variable satisfying every `such that` constraint, optimal for
the objective if one is given. Savile Row reports it in Essence′ terms, translating back
from whatever the target solver said.

That back-translation is worth noting for differential testing: comparing this project's
SMT model against Savile Row's answer means comparing in Essence′ variables, not in the
target solver's — the same projection question `flatzinc.md` §2.4 raises about
`output_var`.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| `find x : bool` | `VarDecl{name, Sort::boolean()}` | none | `exact()` |
| `find x : int(l..u)` | `VarDecl{integer(), lower_bound, upper_bound}` | none | `exact()` |
| `find x : int(a, b, c)` | `VarDecl` bounds + membership `Constraint` | none | `exact()` (§2.2) |
| `find m : matrix indexed by […] of D` | — | `SortKind::ARRAY` | — |
| `given` / `letting` | substituted before lowering | none | `exact()` |
| `where` (parameter validity) | checked, not lowered | none | `exact()` — a failed `where` is `E_TYPE`, not a translation |
| `+ - *` | `Op::ADD` / `SUB` / `MUL` | none | `exact()` |
| `/`, `%` | **§4.3** | `Op::DIV_TRUNC`, `Op::MOD_TRUNC` | `exact()` if corrected |
| `|x|` | via `ITE` | `Op::ABS` or `Op::ITE` | `exact()` |
| comparisons | `Op::EQ` / `LT` / … | none | `exact()` |
| `/\ \/ !` | `Op::AND` / `OR` / `NOT` | none | `exact()` |
| `->`, `<->` | expressible via the above | `Op::IMPLIES`, `Op::IFF` for directness | `exact()` |
| `q[i]` with a constant index | the element's `VarDecl` directly | none | `exact()` |
| `q[i]` with a variable index | `element` encoding (`flatzinc.md` §4.3) | `ExprKind::ARRAY_ACCESS` | `exact()` |
| `forall i : D . e` | **expanded** into a conjunction (§4.2) | none, given the expansion | `exact()` |
| `exists i : D . e` | expanded into a disjunction | none | `exact()` |
| `sum i : D . e` | expanded into an n-ary `Op::ADD` | none | `exact()` |
| `[ e | i : D, c ]` | expanded | `ExprKind::COMPREHENSION` if kept unexpanded | `exact()` |
| global constraints | cluster A's shared decomposition library | a call form | mostly `exact()` |
| `minimising e` | `Objective{MINIMIZE, e}` (`include/somtparser/hir/hir.h, 981-986`) | none | `exact()` |

---

## 4. Semantic gaps and encoding choices

### 4.1 The collision with Savile Row, and what is actually new

Savile Row does, for Essence′, a large part of what this project proposes to do for
twenty-two languages: it reformulates models, it chooses among alternative encodings
(the CP2020 SR-SMT work gives `alldifferent` two encodings, which
`docs/related-work-round2.md` §3 records), and it emits SMT-LIB. Any claim of the form
"we translate Essence′ to SMT" is already true of Savile Row and better developed there.

What is different, stated so each item is checkable rather than rhetorical:

| Claim | Why it is not Savile Row's | Where it lives in this codebase |
|---|---|---|
| **Fidelity is recorded per instance, per choice** | Savile Row selects an encoding; it does not emit a machine-readable statement of *what the selected encoding preserves*. An under-approximation and an exact decomposition are not distinguished in its output. | `Uir::Fidelity` and `EncodingChoice`, aggregated in `TranslationReport` |
| **One IR across twenty-two languages** | Savile Row's reformulations are Essence′-specific by construction. A decomposition written here for `allDiff` serves MiniZinc, FlatZinc, XCSP3 and Essence′ alike. | `Uir::Hir`, cluster A |
| **The choice is data, not a decision** | Savile Row's goal is to pick well and proceed; the goal here is to *vary* the choice and measure. A profile is a configuration, hashed into provenance so a result row names the configuration that produced it. | `Uir::EncodingProfile`, `Provenance::profile_content_hash` |
| **Cross-paradigm comparison is the point** | Savile Row targets a solver; this project's question is which paradigm answers which domain, which needs the same instance under several targets. | `docs/languages-scoping.md` §6, §7 |

And what is **not** claimed, so a reviewer does not have to find it:

- Not better encodings than Savile Row's. Its reformulation work is deeper than anything
  planned here.
- Not a better Essence′ frontend. Savile Row *defines* the language (§1).
- Not novelty in translating CP to SMT. `docs/related-work-round2.md` covers the prior art;
  fzn2smt and SR-SMT got there first.

**The productive framing** is that Savile Row is the *oracle*, not the competitor. Because
it emits SMT-LIB from the same source, an Essence′ instance gives two independent SMT
scripts for the same model, and any disagreement between them is a bug in one of the two —
the cheapest differential test available in the entire batch, and available for no other
language here. That is a reason to implement Essence′ **early** despite its weak corpus,
and it is the opposite of the conclusion the collision risk suggests on its own.

### 4.2 Quantifiers are bounded, so they expand

`forall i : int(1..n) . e` looks like cluster C — a genuine quantifier, needing
`ExprKind::FORALL` and the engine's `mkForall`. It is not, because **the domain is always
finite and known**: `n` is a parameter, substituted before lowering, so the quantifier
ranges over a concrete set.

| Option | Form | Fidelity | Cost |
|---|---|---|---|
| **Expand** | `⋀_{i=1..n} e[i]` | `exact()` | O(n) nodes; the model's size becomes the instance's size |
| Emit a real SMT quantifier over a bounded index | `∀i. (1 ≤ i ≤ n) → e[i]` | `exact()` | small script, but hands the solver a quantified formula for something ground; usually much worse to solve |

Expansion is right, and it is what every CP toolchain does. The consequence to plan for is
**size**, not fidelity: a nested `forall i, j` over `n = 1000` is 10⁶ constraints, and
`dimacs-cnf.md` §4.4's memory arithmetic applies (each `Hir::Expr` is on the order of
140 bytes before its `args` buffer, `include/somtparser/hir/hir.h`). Interning
repeated subexpressions matters here for the same reason it matters for DIMACS.

So Essence′ needs **no quantifier surface** — a useful result, because it means cluster A
(arrays and globals) is its whole HIR cost, shared with three other languages, and it
touches none of cluster C.

### 4.3 Arithmetic and table constraints

The [Savile Row manual](https://arxiv.org/html/2201.03472v1), sections 2.1.6,
2.1.9 and 3, specifies floor division and the complementary remainder:
`(-3)/2=-2`, `3/(-2)=-2`, and `3%(-2)=-1`. The frontend uses the shared
`DIV_FLOOR`/`MOD_FLOOR` operators and retains division-by-zero definedness.
Boolean operands coerce to integers in numeric contexts (`false=0`, `true=1`);
integers are not implicitly accepted as Boolean conditions.

`**` supports constant integer exponents up to the finite elaborator limit,
with right associativity and precedence above unary minus. Negative exponents
and `0**0` are undefined at the nearest Boolean relation. Variable exponents
remain explicitly unsupported. `alldifferent` is accepted as an `allDiff`
alias; the legacy CSPLib implication spelling `=>` is also accepted.

`table(scope, tuples)` lowers through the shared HIR table relation. The scope
may be a list, comprehension, or decision matrix slice; tuples may be a constant
two-dimensional literal or named matrix. An empty tuple list is false. Tuple
comprehensions and higher-dimensional tuple slices are not yet supported.

`gcc(targets, values, counts)` constrains the exact number of occurrences of each
listed value; unlisted values remain allowed. `values` must contain only parameter
expressions, and it must have the same length as `counts`. Repeated target entries
contribute separately, and duplicate entries in `values` retain each corresponding
count equality. Constant and decision matrices can supply slices such as
`requirements[day, ..]`; slices preserve their declared index domains and the same
partiality rules as matrix reads.

### 4.4 Matrices are the language's array question

Essence′ matrices are multi-dimensional and their index domains need not start at 1 —
`matrix indexed by [int(0..n-1), int(1..m)]`. FlatZinc flattens to 1-D with base 1
(`flatzinc.md` §2.2) and XCSP3 uses size vectors (`xcsp3.md` §2.2); Essence′ needs the
general case.

That looked like an argument for an index-set-aware `SortKind::ARRAY`, distinct from
SMT-LIB's. **It is not, and the question was settled on 2026-08-12**: an SMT-LIB array is a
*total* function, so an index set is a constraint on which indices are constrained rather
than a property of the sort. `matrix indexed by [int(0..n-1)]` is one array plus
`∀i. 0 ≤ i < n → …`. One array type, matching SMT-LIB's, shared by clusters A and F. See
`docs/hir-design-decisions-2026-08-12.md` §3.1.

**Implemented 2026-09-20.** More than one index domain is flattened row-major, the last
dimension varying fastest — the convention MiniZinc's `flatIndex` uses. One dimension keeps
the *source* index, so `q[3]` is still `(select q 3)`.

Unlike a parameter array, whose cells fold to literals and never reach the output
(`mps.md` §4.7), a decision matrix *is* emitted, so nothing in the script distinguishes a
flattened two-dimensional matrix from a one-dimensional one and a reader of the output alone
cannot recover the source shape. The flattening is therefore an `EncodingChoice`
(`matrix-flatten-row-major`), recorded per matrix.

Three consequences that a plausible implementation gets wrong while still translating:

* **each subscript is checked against its own domain**, not the flattened offset —
  `q[1,5]` on an `int(1..4)` second dimension lands inside the next row, in range for the
  flat vector and wrong for the model;
* **`allDiff` ranges over the whole flattened space**, not dimension one's span, which would
  constrain the first row and leave the rest free — strictly weaker and sound-looking;
* **the projection names observables by the subscript tuple**, `q[2,3]` rather than the
  offset `q[7]`, because the projection is what a reader maps a solution back through.

A non-constant subscript on a multi-dimensional matrix was refused by name until
2026-09-22, on the grounds that this frontend expands its quantifiers, so a surviving
variable subscript meant something it had not been taught to read. That was true of the
quantifiers and false of the corpus: Conjure writes subscripts that are *expressions over*
comprehension variables — `m[q1 + 1, q2]` — which expansion turns into a term, not a
literal.

**Implemented 2026-09-22** by building the offset instead of folding it
(`flatOffsetTerm`, `languages/essence/src/essence.cpp:2365`). It is the same Horner
recurrence `Matrix::offsetOf` evaluates, `off = off * size_k + (sub_k - lo_k)`, emitted as
HIR arithmetic; the engine's builders fold it back to the literal `offsetOf` would have
produced whenever the subscripts are in fact constant, so the two paths cannot disagree
about the layout.

Two details carry the correctness:

* **soundness is compositional, and no bound on the offset is needed or would suffice.**
  The per-subscript check above is what carries it: a non-constant subscript has its own
  declared bounds carried as a local definition condition. At the nearest source Boolean
  expression an undefined value makes that relation false; a surrounding negation can
  make it true. The Horner fold is used only where every source index is defined. Bounding the *offset* instead would
  re-introduce exactly the `q[1,5]` error above.
* **the all-constant path still calls `offsetOf`**, because `(select a 5)` is checkable in
  a way that `(select a (+ (* 0 3) 5))` is not — the same argument the MiniZinc frontend's
  `flatIndex` makes. The recurrence is therefore written twice on purpose, and pinned by a
  test asserting that the two paths produce the same script on a matrix whose dimensions
  start at *different* places, so that a wrong `lo_k` cannot agree with the right one.

### 4.5 Sparse domains

Identical to `xcsp3.md` §4.4 in mechanism and consequence: `int(1, 3, 5)` cannot live in
`VarDecl`'s two bounds, must become a membership constraint, and reading it as a range is
unsound. Not repeated here.

### 4.6 Globals: cluster A's shared work

`allDiff`, `gcc` (global cardinality), `table`, `atmost`/`atleast`,
`alldifferent_except` — a smaller catalogue than XCSP3's (`xcsp3.md` §2.3) and largely a
subset of it. The decomposition library is written once for cluster A
(`minizinc.md` §4.3); this document adds no new member to it.

**Written once, and until 2026-08-17 used by one language.** This frontend expanded `allDiff`
itself, into an n-ary `DISTINCT` over materialised selects — terser output than the pass
produces, and also this frontend deciding an encoding, so `--profile quantified` on an
Essence′ model was accepted and did nothing. It now emits a `Hir::Global` in the **indexed**
shape, which it can do because it declares a real HIR array; XCSP3 and FlatZinc flatten their
variable vectors to scalars and so reach only the list shape, which is pairwise under both
styles because a list of terms has no index set to bind over.

So of the four cluster-A languages, **two vary with the encoding style** (MiniZinc, Essence′)
and two are routed through the pass and recorded but do not vary (XCSP3, FlatZinc). That is
the honest form of the claim above, and the remaining half is a matter of those two declaring
arrays rather than of the pass library.

The one Essence′-specific note is that Savile Row *already decomposes these*, differently,
and its choice is visible in its SMT-LIB output — which under §4.1's framing is not a
duplication but a second data point per instance.

---

### 4.7 A generator whose domain is a matrix

`basic_powerSetComprehensionDirect.eprime` writes

```
and([ body | t : matrix indexed by [int(1..1 + (b - a))] of int(a..b + 1),
             <guard over t>, <guard over t> ])
```

which is a quantifier over a **function space**: `t` ranges over every matrix of
that shape — with the corpus's `a = 1, b = 4`, all 5⁴ = 625 of them.

**Implemented 2026-09-22 by expanding it**, which is §4.2's strategy and not a
new one: the space is finite, and this frontend already expands every generator
it reads. A matrix generator binds its variable to a `ConstMatrix` — index
domains plus a row-major cell vector — and the tuple loop walks scalar and
matrix variables in one mixed-radix enumeration, so the two kinds cannot get out
of step with each other.

Four things are worth stating because each is a place the obvious version is
wrong:

* **the cost is the count, so the count is checked first.** The space is
  |values|^|cells|; a `matrix indexed by [int(1..8)] of int(1..9)` is 43 million
  bodies. It is refused by name, against `kElaboratorLimit`, and the product is
  computed by repeated division rather than `pow` — the count overflows `long
  long` for shapes a reader may plausibly write, and an overflow would wrap into
  a small number and expand happily.
* **a constant matrix is read before a declared one.** `matrices_` records the
  shape of a *decision* matrix and its reads lower to `(select m offset)`; a
  cell of a bound one is a literal. Checking the wrong map first emits a select
  on a variable the model never declared.
* **cell addressing goes through `Matrix::offsetOf`**, including its
  one-dimension short circuit, so a constant matrix and a declared matrix of the
  same shape address their cells identically. This is the third site that has to
  agree about the layout (§4.4), and it agrees by calling the other two's
  function rather than by repeating the recurrence.
* **the guards are evaluated through the expression parser.** Conjure's guards
  over a bound matrix are *folds* — `and([t[q] < t[q+1] \/ t[q] = b+1 | q :
  int(1..3)])` — and the token-level `constGuard` reads comparisons and
  connectives, not comprehensions. Rather than give it a second comprehension
  expander, the guard is parsed by `expr()`, which already has one, and the
  resulting HIR is evaluated as a constant. It is tried only after the token
  path and only when a matrix generator is present, so no existing
  comprehension changes which reader sees its guards.

**The tests assert counts, not satisfiability.** The failure this is written
against — enumerating part of the space — produces a script that is well formed,
translates, and is satisfiable, so "it translated" and "cvc5 said sat" are both
passed by an over-approximation that drops the quantifier entirely. Each case
instead pins how many conjuncts the expansion produced, with a control one value
narrower, and a two-cell case where a decoder that walked one radix wrongly stops
covering the space.

The alternative encoding was considered and not taken: `forall t. domain(t) /\
guards(t) -> body(t)` with `t` an HIR array is compact and is what Savile Row
means, but it expresses only the `and`/`or` folds — `sum` over a quantified
variable is not a term — so it would have covered part of the construct and left
the rest refused, with two encodings to keep in agreement. Expansion is exact
for all three folds and bounded by a stated limit.

## 5. New HIR surface this format forces

| Surface | Needed for | Also needed by |
|---|---|---|
| `SortKind::ARRAY` + `ExprKind::ARRAY_ACCESS`, **with index sets** (§4.4) | `matrix` declarations and indexing | MiniZinc, FlatZinc, XCSP3 |
| a global-constraint call form | §4.6 | all of cluster A |
| `Op::DIV_TRUNC`, `Op::MOD_TRUNC` | §4.3 | MiniZinc, FlatZinc, XCSP3, Boogie, CryptoLine |
| `Op::ABS` | `|x|` | MiniZinc, FlatZinc, XCSP3 |
| `Op::ITE` | `|x|`, `element`, conditional expressions | FlatZinc, XCSP3, MiniZinc |
| `Op::IMPLIES`, `Op::IFF` | `->`, `<->` | MiniZinc, XCSP3 |
| `ExprKind::COMPREHENSION` | **only if comprehensions are kept unexpanded** (§4.2) | MiniZinc |

**Not needed**: any quantifier surface (§4.2), sets (Essence′ has them only via Conjure's
refinement, which happens above this level), and real literals — Essence′ is integer and
Boolean, so unlike `lp.md` and `mps.md` it does not need `ExprKind::LIT_REAL`, which landed on 2026-08-12 for their sake rather than for this format's.

Essence′ therefore forces **nothing that MiniZinc, FlatZinc and XCSP3 have not already
forced**, with one refinement: §4.4's index-set-aware arrays. That is its whole marginal
HIR cost, and it explains why `docs/languages-scoping.md` §3.2 puts its 2.0× on grammar
rather than on new features.

---

## 6. Fidelity summary

**Exact — the entire language, in principle.** Every construct in §3 maps exactly once
cluster A's surface exists: integer and Boolean variables, sparse domains as membership,
matrices, arithmetic, comparisons, connectives, expanded quantifiers, comprehensions,
element access, and the objective.

**Inherently lossy: nothing intrinsic to Essence′.** Losses come from encoding decisions
shared with the rest of cluster A — a global constraint whose only practical encoding
bounds a domain (`underApprox` with `Bound::DOMAIN_CUT`,
`include/somtparser/translation/fidelity.h:92`) — not from anything the language itself expresses
and SMT cannot.

**Ways to make it lossy by mistake**:

- Reading a sparse domain `int(1, 3, 5)` as the range `int(1..5)` (§2.2, §4.5).
  **Unsound: admits solutions the model forbids.**
- Emitting SMT-LIB `div`/`mod` for Essence′'s `/` and `%` without confirming the convention
  (§4.3). **Silent.**
- Translating the model without its `.param` file — refused by construction today (§2.1),
  and the refusal must survive `acceptsDataFiles()` being switched on.
- Assuming matrix indices are 1-based (§4.4).

**Not a fidelity question, and the one that governs how this arm is reported**: Essence′ has
no competition corpus (§1), so an Essence′ result cannot claim a comparison against a
published baseline the way the other twenty-one can. Report it as a translation-fidelity
and coverage result, and use Savile Row as a differential oracle (§4.1) rather than as a
ranking to beat.

---

## 7. References

**Language and system**

1. Savile Row manual and Essence′ language description.
   <https://savilerow.cs.st-andrews.ac.uk/> — **version not re-confirmed in this pass**;
   note that the implementation, not a standard, defines the language (§1).
2. P. Nightingale, Ö. Akgün, I. P. Gent, C. Jefferson, I. Miguel, P. Spracklen,
   *Automatically improving constraint models in Savile Row*, Artificial Intelligence, 2017.
3. Conjure (Essence → Essence′ refinement), for the level above this one.

**Corpus**

4. CSPLib and the Savile Row distribution's instances. **No competition archive, no ranked
   baseline** — see §1 and `docs/languages-scoping.md` §1.1, §3.2, §7.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster A), §3.2 (2.0×, and the corpus caveat),
   §6 (the second filter), §7 (the competition audit).
6. `docs/related-work-round2.md` §3 (SR-SMT's two `alldifferent` encodings, and the prior
   art §4.1 declines to claim novelty against).
7. `docs/languages/minizinc.md` §4.1 (the `div`/`mod` conventions), §4.3 (cluster A's
   decomposition library).
8. `docs/languages/xcsp3.md` §2.2 and §4.4 (sparse domains), §2.3 (the global catalogue).
9. `docs/languages/flatzinc.md` §2.2 (1-D flattening), §2.4 (comparing in the source
   language's vocabulary), §4.1 (measuring somebody else's encoder), §4.3 (`element`).
10. `docs/languages/dimacs-cnf.md` §4.4 (the memory arithmetic §4.2 depends on).
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `include/somtparser/translation/language.h`, `src/translation/translate.cpp`.


### Relational undefinedness (corrected 2026-09-23)

The [Savile Row 1.11.1 manual](https://www-users.york.ac.uk/peter.nightingale/savilerow/releases.html),
section 3 and Table 5, specifies relational semantics. A partial integer expression
propagates undefinedness through arithmetic to its nearest Boolean expression, which
becomes false. A Boolean matrix read is itself that boundary. Consequently `x/0 != y`
is false while `!(x/0 = y)` is true. The prior global strict-definedness constraints
were a frontend bug, and the previous claim that these two answers showed an
inconsistent reference semantics was incorrect.

The parser now retains local definition conditions separately from declaration-domain
constraints. Source comparisons, Boolean matrix reads, and source Boolean operators
close their own conditions before HIR simplification. Generated comparisons inside
`min`, lexicographic expansion, and other encodings do not introduce source boundaries.
Out-of-range constant reads follow the same rule as variable reads. Numeric
`catchUndef(e, constant)` uses the condition to select a fallback; objective expressions
must be defined. Empty numeric minima/maxima are undefined. Finite comprehension
filters discard excluded bodies before elaboration.

`test/python/test_essence_partiality.py` checks these distinctions by solving both
satisfiable and contradictory constraints, including the unchanged `basic_set07`
corpus file. Reference solver evidence is recorded separately from these checks.

Objective labels are selected after all declarations and parameters have been read. Source names such as `obj`, including scalar and matrix names declared after the objective, remain distinct from the generated OMT objective binding.

The shared HIR numeric constructors normalize a valid leading `+` without rounding integer, decimal, or rational literals; malformed numeric spellings remain errors.
