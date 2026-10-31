# QCIR-G14 — non-prenex, non-CNF quantified Boolean formulas

**Date**: 2026-08-12
**Status**: **implemented** (`languages/qcir/`, `test/languages/test_qcir.cpp`), added by
`docs/language-expansion-2026-08-12.md` §3. The second language in tree after MiniZinc, and
the first written document-first: every obligation in the block below was written from the
standard before any code existed, and each is now a fixture in `languages/qcir/instances`.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster **C** (quantifiers), alongside
QDIMACS. Estimated cost **0.5×**, the cheapest entry in the batch.
**Sources**: the QCIR-G14 standard (QBF Gallery 2014, <https://www.qbflib.org/qcir.pdf>),
read directly for this document; every syntactic claim below is from its BNF or its §2.2
"Details" and is marked where the standard's wording matters.


<!-- implicit-constraints:
  a non-gate variable that is neither quantified nor in the free block => is a FREE variable by default (standard §2.2, "Quantifier Alternations"); the frontend must materialise it as a top-level declaration; QDIMACS instead adds an outermost existential binder for unquantified matrix variables (§4.1)
  an `and` gate with zero inputs => the constant true; an `or` gate with zero inputs => the constant false (standard §2.2, "Truth Constants"); emit mkBool, never mkOp(AND, {}), which throws (src/hir/hir.cpp) -- the same trap dimacs-cnf.md §4.1 records for the empty clause, with the opposite polarity (§4.2)
  gate definitions not reachable from the output => are ignored by the semantics (standard §2.2, "Output"); they must not become constraints, and must not be counted in the reported statistics, or two files denoting the same formula report different sizes (§4.3)
  a gate variable must be defined before it is used => the circuit graph is acyclic by construction (standard §2.2, "Gate Variables"); a frontend still has to check it, because the property is what makes a single bottom-up pass correct and a malformed file would otherwise loop (§4.4)
  a gate variable occurs exactly once on the left of `=` and never in `free` or a quantifier block => gate variables and input variables are disjoint namespaces; merging them lets a redefinition pass as a constraint (§4.4)
  the format-id `#QCIR-G14 n` carries a variable count n => the file claims to be in cleansed form and to use integer names <= n (standard §2.3); n is a checkable claim about the file, not a hint, and a mismatch means the producer and consumer disagree about which dialect this is (§4.5)
  a quantifier gate `g = exists(v1, v2; lit)` binds v1, v2 only inside lit => the quantifier is an ordinary subterm at an arbitrary circuit position, so the prefix is not the semantics the way QDIMACS's is (§2.2)
  cleansed form requires a gate with a quantified subformula to be used at most once => a quantified subcircuit may not be shared; a hash-consing IR shares it by construction, so sharing must be measured rather than assumed harmless (§4.6)
  `ite(x, y, z)` is defined as (x AND y) OR (NOT x AND z) => the standard fixes the expansion, so a frontend must not substitute a different one; Op::ITE landed for this format, so the frontend emits the operator and the expansion stays available as the recorded alternative (§4.7)
  keywords are case-insensitive but variable names are case-sensitive => `AND` and `and` are one gate type while `V1` and `v1` are two variables; one case-folding pass over the whole token stream is wrong (§2.1)
-->

**Headline result**: QCIR is the cheapest language left to add, and it is not redundant with
QDIMACS. It measures something QDIMACS structurally cannot — `qdimacs.md` §4.2 records that a
CNF matrix arrives as **one** n-ary `AND` with 10⁵ children, so the QDIMACS arm holds
*structure* fixed at "none". QCIR arrives already structured, over the same benchmark family
and the same solvers. The pair is the `EncodingProfile::style()` question — ground versus
quantified, size versus solvability — asked along a second axis, and neither half answers it
alone.

**Unquantified variables require distinct representations.** QCIR retains them
as free non-gate variables. QDIMACS 1.1 accepts unquantified matrix variables too,
but binds them existentially at the outermost level. See the
[QDIMACS specification](https://www.qbflib.org/qdimacs.html), Input format,
third additional constraint. The earlier claim that QDIMACS must refuse these
inputs was incorrect; both the frontend and its paired tests have been corrected.

---

## 1. What the format is

QCIR — "Quantified CIRcuit" — is QBFLIB's non-prenex, non-CNF format, based on the ISCAS-89
circuit format. A file is a format identifier, a quantifier prefix, an output declaration,
and a list of gate definitions.

| | |
|---|---|
| **Standard** | QCIR-G14, QBF Gallery 2014, dated 8 April 2014 |
| **Maintainer** | the QBF Gallery organisers; published at qbflib.org |
| **Corpus** | QBFEVAL's non-prenex non-CNF track |
| **Reference tools** | GhostQ (and its QCIR-to-QDIMACS converter), RAReQS-NN, QuAbS |
| **Licence** | *not settled by this research.* Pin before implementation, as `docs/languages-scoping.md` §1.2 requires. |

The standard defines **two** dialects: a general one, and a **cleansed** form with syntactic
restrictions that make it easier for solvers to consume. Which one a file is in is declared
by the format-id line (§4.5), and they differ in ways a parser must act on — cleansed files
contain no `xor` and no `ite` gates at all.

### 1.1 The grammar

Reproduced from the standard's BNF, because several obligations below are only visible in it:

```
qcir-file     ::= format-id qblock-stmt output-stmt (gate-stmt nl)*
format-id     ::= #QCIR-G14 [integer] nl
qblock-stmt   ::= [free(var-list) nl] qblock-quant*
qblock-quant  ::= quant(var-list) nl
var-list      ::= (var,)* var
lit-list      ::= (lit,)* lit | ε
output-stmt   ::= output(lit) nl
gate-stmt     ::= gvar = ngate_type(lit-list)
                | gvar = xor(lit, lit)
                | gvar = ite(lit, lit, lit)
                | gvar = quant(var-list; lit)
quant         ::= exists | forall
ngate_type    ::= and | or
lit           ::= var | -var | gvar | -gvar
```

Two productions carry most of this document. `lit-list ::= … | ε` is what makes an empty
`and()` legal, and `gvar = quant(var-list; lit)` is the **quantifier gate** — a quantifier at
an arbitrary position in the circuit, which is what "non-prenex" means concretely.

---

## 2. Semantics — what a file means

### 2.1 Lexical

Any line beginning with `#` is a comment — *including*, syntactically, the format-id line,
which is why the first line is read specially rather than skipped with the rest. Whitespace,
newlines and tabs are free.

The standard requires the format identifier on line 1. Some QBFEVAL 2022
published inputs omit it. The explicit parse option `allow_missing_header=true`
accepts that dialect, emits a warning, and interprets the unchanged body as
general QCIR (without claiming cleansed form). The default remains strict.
An explicitly different or malformed QCIR format identifier is still rejected.
An initial quantifier on line 1 is retained. Numeric variable names are emitted
as quoted SMT-LIB symbols at both their binders and their occurrences.

Keywords are **case-insensitive**; variable names are **case-sensitive**. A frontend that
lowercases the token stream once, which is the obvious way to handle `AND` versus `and`,
merges `V1` and `v1` into one variable and produces a formula with fewer variables than the
file has. The case fold belongs on keyword recognition only.

### 2.2 The prefix is not the semantics

This is the substantive difference from QDIMACS. In QDIMACS the prefix *is* the quantifier
nesting and reordering two adjacent blocks of different quantifiers changes the answer
(`qdimacs.md` §2.2). In QCIR the prefix is a convenience for prenex files, and a quantifier
gate

```
g2 = exists(x1, x2; g1)
```

binds `x1`, `x2` **only inside** `g1`. The standard's own non-prenex example makes the shape
plain:

```
#QCIR-G14
forall(z)
output(g3)
g1 = and(x1, x2, z)
g2 = exists(x1, x2; g1)
g3 = or(z, g2)
```

which is `∀z. z ∨ ∃x1 ∃x2. (x1 ∧ x2 ∧ z)`. Note that `x1` and `x2` appear in `g1` and are
bound by `g2`, one level up — so a frontend cannot decide whether an occurrence is free or
bound by looking at the gate it occurs in. Scope is determined by the path from the output,
which is the reason the traversal in §4.4 is rooted at `output` rather than at the gate list.

The standard also permits **consecutive quantifier blocks of the same type**, which QDIMACS
does not. Merging them is sound and changes no answer, but the *alternation depth* is what
QBF complexity is organised around and what `qdimacs.md` §4.3 argues the experiment must
record — so the merge has to happen before the depth is counted, or two files denoting the
same formula report different depths.

### 2.3 Truth constants

An `and` gate with zero inputs is `true`; an `or` gate with zero inputs is `false`. This is
the standard's §2.2, not an inference. It is also the trap `dimacs-cnf.md` §4.1 records with
the polarity reversed — there, an empty *clause* is `false` — and it has the same mechanical
consequence here: `mkOp(Op::AND, {})` throws (`src/hir/hir.cpp`), so the frontend must
emit `mkBool(true)` (`include/somtparser/hir/hir.h`) and never route an empty gate
through the n-ary builder.

### 2.4 Free variables, and what closing them costs

The standard says a tool that does not support free variables "may assume that these
variables are existentially quantified in the outermost quantifier block". That permission is
about *satisfiability*, and taking it silently is a fidelity loss this project is built to
record: a QBF with free variables asks for which assignments to them the formula holds, and
existential closure asks only whether one exists. If the frontend closes, it must record a
`Fidelity` that is not `exact()` — the answers to `check-sat` agree, the answers to the
question the file asks do not.

---

## 3. Construct → HIR mapping

| QCIR construct | HIR | New surface | Fidelity |
|---|---|---|---|
| `free(v1, v2)` | `VarDecl{name, Sort::boolean()}` (`include/somtparser/hir/hir.h`) | none | `exact()` |
| unquantified non-gate variable | the same — it *is* free (§4.1) | none | `exact()` |
| `exists(v1, v2)` prefix block | `ExprKind::EXISTS` (`include/somtparser/hir/hir.h`) over the whole body | none | `exact()` |
| `forall(v1)` prefix block | `ExprKind::FORALL` (`include/somtparser/hir/hir.h`) | none | `exact()` |
| `g = exists(v; lit)` quantifier gate | the same `ExprKind::EXISTS`, at the position the gate occupies | none | `exact()` |
| variable occurrence under a quantifier | `ExprKind::BOUND_VAR` (`include/somtparser/hir/hir.h`) | none | `exact()` |
| `g = and(a, b, c)` | `Op::AND` | none | `exact()` |
| `g = or(a, b)` | `Op::OR` | none | `exact()` |
| `g = and()` / `g = or()` | `mkBool(true)` / `mkBool(false)` | none | `exact()` |
| `-a` (negated literal) | `Op::NOT` | none | `exact()` |
| `g = xor(a, b)` | **`Op::XOR`**, or the expansion in §4.7 | `Op::XOR` | `exact()` either way |
| `g = ite(a, b, c)` | **`Op::ITE`**, or the standard's expansion | `Op::ITE` | `exact()` either way |
| `output(g)` | the single top-level `Constraint` | none | `exact()` |
| a gate unreachable from `output` | **dropped** (§4.3) | none | `exact()` — it is not part of the formula |

The column that matters is the third: **almost all of it is empty.** The quantifier surface
landed on 2026-08-12 (`ExprKind::FORALL`, `EXISTS`, `BOUND_VAR`, `mkForall` at
`include/somtparser/hir/hir.h`), and it was built for QDIMACS. QCIR reuses it unchanged,
including at non-prenex positions, because a quantifier in this HIR is an ordinary expression
rather than a prefix attached to a model. That was a design choice at the time and this is
the first language that collects on it.

---

## 4. Semantic gaps and encoding choices

### 4.1 Unquantified variables

QCIR represents unquantified non-gate variables as free Boolean declarations.
QDIMACS adds an outermost existential binder for unquantified matrix variables.
Both inputs are legal, but the resulting HIR structures differ: QCIR can expose
a relation over free variables, whereas QDIMACS represents a closed QBF.

The paired fixtures and `test/languages/test_sat_cross_format.cpp` check this
binding distinction. QDIMACS additionally tests that implicit variables precede
all universal blocks, preserving their allowed dependencies.

### 4.2 Empty gates

`and()` is `true` and `or()` is `false`. Both are legal — `lit-list` derives ε — and both
sound degenerate enough to be omitted from a first implementation, which is exactly how
`dimacs-cnf.md` §4.1's empty clause got its own fixture. The `mkOp` builder throws on an empty
argument list rather than inventing an identity, so the failure is loud rather than silent;
that is why it is a `condAssert` and not a comment. Two fixtures, one per polarity.

### 4.3 Unreachable gates are not constraints

"Gate definitions not connected to the output shall be ignored." A frontend that walks the
gate list and emits each definition as an equality constraint is therefore wrong twice: it
adds constraints the formula does not have, and — because those gates may mention variables
nothing else does — it can change satisfiability outright.

It also corrupts the statistics. `TranslationReport` counts what was emitted, and the
experiment tabulates it; two files denoting the same formula, one with dead gates, would
report different sizes. The traversal must be rooted at `output` and the count taken from what
the traversal reached.

### 4.4 The two structural checks

The standard makes the circuit acyclic *by construction*: a gate variable must be defined
before it is used. That is a syntactic property of a well-formed file, not a semantic one to
be derived, and it is what licenses a single bottom-up pass.

It is also exactly the kind of guarantee that must still be checked, because the guarantee is
about *conforming* files and a frontend meets non-conforming ones. An unchecked use-before-def
turns the bottom-up pass into an unbounded recursion on a hand-edited file. The second check
is the namespace split: a gate variable occurs exactly once on the left of `=`, and never in
`free` or a quantifier block. Keeping gate and input variables in one table lets a
redefinition through as though it were a constraint.

### 4.5 Which dialect is this file in

`#QCIR-G14 6` and `#QCIR-G14` are different claims. The integer says the file is in **cleansed
form**, uses integer variable names, and has at most that many variables (inputs plus gates,
counting a variable once per quantification). Cleansed files also contain **no `xor` and no
`ite` gates at all**.

So the count is a checkable claim, and checking it is worth the four lines: a mismatch means
the producer and the consumer disagree about which dialect the file is in, which is a class of
bug that otherwise surfaces as a variable-count discrepancy three layers away. The frontend
should record the dialect in the `TranslationReport`, because "does structure preservation
help" (§4.8) is a question whose answer may depend on it.

### 4.6 A quantified subcircuit may not be shared — but this IR shares

Cleansed form requires that "gate-variables which have a subformula with quantification are
used at most once". The restriction exists because a shared quantified subcircuit is what
makes non-prenex QBF expensive to process.

The HIR inherits the opposite property. Expressions are immutable and shared
(`include/somtparser/hir/hir.h`'s header comment), and the engine below it hash-conses, so a
repeated subformula becomes **one** node with several parents — automatically, with no way to
opt out per node. For an ordinary gate that is a pure win. For a quantifier gate it means the
translation of a general (non-cleansed) QCIR file can produce a DAG whose shared quantified
nodes are precisely what the cleansed dialect forbids.

This is not a soundness problem — the SMT-LIB formula is the same formula either way, and
sharing a closed subterm is sound. It is a **measurement** problem, and it belongs in the
report: the number of shared quantified subterms is a property of the instance that the
experiment should record rather than average away, because it is the parameter the format's
own designers thought worth restricting.

### 4.7 `xor` and `ite`

Both landed on 2026-08-12, for this format. The expansions remain worth writing down, because
they are what a frontend does when the operators are absent and because the second is
*specified* rather than chosen:

- `xor(a, b)` ≡ `(a ∨ b) ∧ ¬(a ∧ b)`, duplicating both arguments;
- `ite(a, b, c)` ≡ `(a ∧ b) ∨ (¬a ∧ c)` — **the standard's own definition**, so a frontend
  without `Op::ITE` must use this one and not an equivalent of its choosing.

Both are `exact()`. The frontend emits the operators, so the expansions are the recorded
alternative rather than the translation. Cleansed files contain neither gate, and the frontend
refuses one that does (§4.5) — the count on the format identifier is a claim about the body,
and believing the header over the body would let a mislabelled file through.

### 4.8 What the experiment measures

The QDIMACS arm holds structure fixed at none: `qdimacs.md` §4.2 records the matrix arriving
as one n-ary `AND` over 10⁵ children, because that is what CNF *is*. Every question about
whether an SMT solver benefits from seeing structure is unanswerable from that arm alone.

QCIR is the control. Same benchmark family, same solvers, same quantifier surface — and the
input arrives as a circuit. Three quantities are worth recording per instance and are cheap
once the frontend exists: quantifier alternation depth (after merging same-type blocks, §2.2),
the gate count reachable from `output`, and the maximum fan-out, which is the sharing §4.6
describes.

The comparison also has an independent oracle. GhostQ's QCIR-to-QDIMACS converter turns a QCIR
file into the format the other arm reads, so one source file yields two SMT scripts by
different routes; disagreement localises a bug rather than merely appearing as a discrepancy.
That is the `essence-prime.md` §4.1 oracle argument, available here without building anything.

---

## 5. New HIR surface this format forces

**None outstanding.** Two were needed and both landed on 2026-08-12:

| Surface | Needed for | Status |
|---|---|---|
| `Op::XOR` | `xor` gates (general dialect only) | landed |
| `Op::ITE` | `ite` gates (general dialect only) | landed |

Cluster C was paid for by QDIMACS; the quantifier surface handled non-prenex positions with no
change at all, because a quantifier here is an expression and not a prefix. That was a design
claim when this document was written and is now a tested one: the standard's own non-prenex
example (`instances/ok/non_prenex.qcir`) translates with the `exists` inside the `forall`'s
body, which is what the format means and what a prefix-shaped IR could not have expressed.

### 5.1 What building it confirmed, and what it changed

**§4.6's prediction held, and it is a measurement rather than a defect.** The frontend
deliberately does *not* memoise quantifier gates — each use is rebuilt, so every binder
occurrence is constructed inside exactly one scope. The engine then hash-conses two
structurally identical `exists` terms back into one node and folds `(and E E)` to `E`. Sharing
of quantified subterms is therefore not something this layer can opt out of, exactly as §4.6
said; the test asserts the semantics (which names are bound, which are free, that the script
re-parses) rather than a property the translation does not control.

**One thing this document got slightly wrong.** §4.4 says the definition-before-use rule makes
the circuit acyclic "by construction". True of conforming files, and the document said so — but
it is worth being blunter than it was: the frontend's traversal is rooted at the output and
walks bottom-up, and on a non-conforming file that recursion does not terminate. The cycle
check is not defensive tidiness, it is what makes the walk correct at all
(`instances/reject/cycle.qcir`).

## 6. Fidelity summary

| Route | `sound` | `complete` | `preserves_optimum` | Bound |
|---|---|---|---|---|
| gates, prefix quantifiers, quantifier gates | ✓ | ✓ | ✓ (no objective) | — |
| empty `and`/`or` as truth constants | ✓ | ✓ | ✓ | — |
| `xor`/`ite` by the standard's expansion | ✓ | ✓ | ✓ | — |
| dropping gates unreachable from `output` | ✓ | ✓ | ✓ | — |
| **existentially closing free variables** | ✓ for `check-sat` | ✓ for `check-sat` | — | **not `exact()`**: it answers a different question (§2.4) |

Every route but the last is `Fidelity::exact()`. The last is the only place where a QCIR
translation can lose something, and the standard explicitly permits it — which is why it has
to be recorded rather than assumed away.

---

## 7. References

1. *QCIR-G14: A Non-Prenex Non-CNF Format for Quantified Boolean Formulas*, QBF Gallery 2014,
   8 April 2014 — <https://www.qbflib.org/qcir.pdf>. Read in full for this document; all
   syntactic and semantic claims above trace to its §2.1 BNF, §2.2 Details, §2.3 Cleansed
   Form, or §3 Examples.
2. C. Jordan, W. Klieber, M. Seidl, *Non-CNF QBF Solving with QCIR*, BNP 2016 — the QCIR
   tooling and solver landscape.
3. QBFEVAL tracks, PNCNF (QCIR) alongside PCNF (QDIMACS) — QBFEVAL'16/'17 report.
4. GhostQ QCIR-to-QDIMACS converter — <https://www.wklieber.com/ghostq/qcir-converter.html>.
   The oracle of §4.8.

**Not settled by this research**: the licence of the QCIR corpus and of the standard document
(`docs/languages-scoping.md` §1.2 requires this before implementation); QBFEVAL's current
edition and whether the non-prenex track still runs; whether the QBF Gallery's promised
cleansing tool is still available.
