# SMT-LIB 2 — the baseline, and the one language that loses fidelity by entering the HIR

**Date**: 2026-08-12
**Status**: **implemented** (`languages/smtlib2/`). §4.1 was re-measured on 2026-08-14 and
its earlier table, which said the HIR carried none of these theories, is superseded.
language with a complete, mature frontend already in tree — the whole of `src/frontend/`.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster **J** ("None"), §3.2 (cost
**0.2×**, "already the native format; round-trip self-test only"), §4.

<!-- proposed-hir: ExprKind::LET -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

<!-- implicit-constraints:
  `(set-logic QF_LIA)` => a restriction the file asserts about itself; a translation that widens it silently is not wrong but is no longer the same benchmark, so the logic must be carried into the report (§2.2)
  a `declare-fun` with zero arguments => a free constant of the model, which must survive translation even if no assertion mentions it, or the model's vocabulary changes (§2.2)
  `define-fun` => a macro, definitionally equal to its body; inlining is exact, but a definition never used still declares a symbol a model must assign (§2.3)
  `(check-sat)` terminates the assertion stack this project reads => commands after `(exit)` are never read, which is why toSmt2 splices objectives *before* it rather than appending (§4.4)
  none of the above is a fidelity question => they are vocabulary and provenance questions, which is what makes this format's real loss (§4.1) invisible to Fidelity
-->

**Headline result of the audit in §4**: every other document in this batch asks "what does
this format have that the HIR lacks?" and answers with a feature list. SMT-LIB 2 asks the
same question and, when this document was written, the answer was **almost everything**: the
engine's `NODE_KIND` enum carried 45 bit-vector kinds, 44 floating-point kinds, 44 string
kinds, arrays (`include/somtparser/core/kind.h:90`), quantifiers (`:151`) and uninterpreted
functions, against a HIR of `SortKind { BOOL, INT, REAL }` and eleven operators.

**That gap is now closed except for one row, and §4.1 below is updated to match.**
As of 2026-08-12 the HIR carries **10 sorts, 15 expression kinds and 107 operators**
(`include/somtparser/hir/hir.h`, `include/somtparser/hir/hir.h`, `include/somtparser/hir/hir.h`): arrays with `select` *and* `store`,
bit-vectors, floating point with a RoundingMode sort and exact literals, strings with the
regular-expression fragment and a RegLan sort, uninterpreted sorts and functions, quantifiers,
exact real literals, and the conversions between all of them.

The five rows this document listed as missing, and what became of each:

| Was missing | Now |
|---|---|
| `Op::STORE` — arrays read-only | **landed.** `select` and `store` both, checked against the index and element sorts separately |
| no real or floating-point literal | **landed.** Both exact and kept as text; `mkReal` takes `1/3` as well as `1.5`, which `lp.md` §4.1 asked for by name |
| RegLan and the regular-expression operators | **landed.** `SortKind::REGLAN`, the three nullary constants as literals, and the twelve operators |
| cross-theory conversions | **landed.** `to_int`/`to_real`, `bv2nat`/`bv2int`/`int2bv`, `fp.to_real`/`fp.to_ieee_bv`/`fp.to_sbv`/`fp.to_ubv`, `to_fp`/`to_fp_unsigned` — each signed/unsigned pair kept apart for the reason `bvult` and `bvslt` are |
| datatypes | **landed.** `SortKind::DATATYPE`, `DatatypeDecl` with constructors and selectors, and the constructor/selector/tester expression kinds. Recursive and mutually recursive declarations both work — see the correction in "landed ≠ readable", and note that mutual recursion additionally needed an *engine* fix: `dumpSMT2` split one declaration group into two commands, and the second named a sort the first had already used |
| **sets** | **landed**, engine and all — see below, and the correction in "landed ≠ readable" |
| **sequences, bags** | **still missing, and not for the reason the others were.** See below |

### "landed" ≠ readable: what this table was measuring

Every "landed" above is a claim about the **HIR** — that a construct has a sort, an
operator and a lowering. On 2026-08-15 that turned out to be a weaker statement than it
reads as, because a construct the HIR carries is still unreachable if
`Lower::ParserToHir` cannot lift it out of a parsed script, and three of these rows were
in exactly that state:

| Row | HIR | Lowering | **Lift** |
|---|---|---|---|
| sets | all nine operators | yes | **no `(Set T)` in `liftSort`** |
| floating-point literals | `LIT_FLOAT` | yes | **decimal-only, which no script contains** |
| `to_fp` / `to_fp_unsigned` | `mkToFp` | yes | **absent** |
| datatypes | sort, `DatatypeDecl`, three expression kinds | yes | **absent — the whole theory** |

The set row is the instructive one. All nine set operators were correctly in the lift's
operator table and not one of them could ever run: a set term needs a set-sorted
argument, so every script naming `(Set Int)` failed at its *declaration*, one line
earlier than any operator was consulted. A table that is complete immediately above an
empty one reads as complete from either end, and neither an enum diff over operators nor
a corpus of files that avoid the theory can see it.

The floating-point row is the same shape inverted. `LIT_FLOAT` required its text to be a
decimal numeral — and a decimal is the one spelling an SMT-LIB script can *never* contain
for a Float, since `1.5` is a Real. The two spellings a script does contain, the
`(fp #b0 #b… #b…)` triple and the five special values, were both refused; `NaN` and the
infinities have no decimal form at all, which is the point of them.

What closed the class rather than the instances is
`test/lowering/test_lift_operator_sweep.cpp`: one row per operator, each asserting
`text → Parser → HIR → Parser → text` comes back equal. §4.1's figures are re-measured
against it.

### The set, sequence and bag row is an *engine* gap, not a HIR gap

Worth stating precisely, because it changes what "add them" costs by an order of
magnitude. The engine has a `SORT_KIND` for each — `SK_SET`, `SK_SEQ`, `SK_BAG`
(`include/somtparser/ir/sort.h:44`) — and that is all it has:

| Theory | Sort | `NODE_KIND`s | `oper_key_map` entries | Builders |
|---|---|---|---|---|
| Set | ✓ | **11**, added 2026-08-12 | ✓ | ✓ |
| Sequence | ✓ | **0** | **0** | **0** |
| Bag | ✓ | **0** | **0** | **0** |
| Datatype | ✓ | 5 | ✓ | via `mkApplyUF` + `getDtFunctionKind` |
| Tuple | ✓ | 5 | ✓ | `mkTupleSelect`, `mkTupleProject`, `mkTupleUpdate` |

Datatypes and tuples were already implemented; a parsed `declare-datatypes` already dumped
back to itself, which is why the HIR could be given a datatype surface at all.

**Sets have since been added to the engine**, because they had a producer: MiniZinc's
`var set of int` was the last item on that frontend's coverage table, and a theory with a
concrete caller is not the speculative kind this project refuses to add. It took the full
ten-step path in `CLAUDE.md`'s "Adding a new operator" — eleven `NODE_KIND`s, the
`oper_key_map` entries, `kindToString`, a `(Set T)` case in `parseSort`, `createSetSort`,
eleven builders, the `parseOper` wiring, the `getArity` buckets, a second `(as …)` form in the
expression parser, and a printer case for the two sort-annotated constants. Two defects turned
up in the doing, both worth recording:

- `Sort::getElemSort()` was array-only and `condAssert`ed on it, so every set builder that
  asked for the element sort threw — and because `Parser::parseStr` catches, the failure
  surfaced as a silent `parse ok = 0` with no message at all.
- `(as set.empty (Set Int))` is a complete *term*, while `((as const T) v)` is an annotated
  *operator*. The existing `as` handling covered only the second shape, so the first fell
  through to the generic symbol lookup and came back "unknown symbol".

**Sequences and bags stay missing**, and the recommendation for them is unchanged: treat each
as its own piece of work, scoped against a language that needs it. Nothing in the batch of 22
does. The other half of the argument is that not every backend implements them — a translation
into a theory most solvers reject narrows the experiment rather than widening it, which is why
"the engine could" is not on its own a reason to.

**Three engine defects surfaced while closing those rows**, all of the same shape — a term
this library can *build* but cannot *read back*, which the dump round-trip property test never
saw because no instance in the corpus exercises the construct:

1. a floating-point constant dumped as a bare decimal, and a bare decimal is a Real;
2. a string constant built through `mkConstStr` dumped without its quotes, because the quotes
   are part of the name only when the *parser* put them there;
3. `fp.to_ieee_bv` present in `oper_key_map` and in the printer but absent from `parseOper`.

The pattern is worth naming: each is a construct reachable only from the programmatic API,
and the corpus that guards the round trip is entirely parser-built. A property test over
API-built terms would have caught all three.

So the §4.1 claim below — that the HIR carries QF_LIA, QF_LRA, QF_LIRA and nothing else — was
true when measured and is now too pessimistic; the honest current statement is that it carries
the quantifier-free and quantified **linear-integer, bit-vector, uninterpreted-function** and
*partial* floating-point and string fragments, and that the array fragment is incomplete for
want of `store`.

So SMT-LIB 2 is the one language in the batch where **going through the HIR loses
information that a direct parse keeps** — and the design spec forbids the direct route on
purpose (§6.1 rule 3: "前端产物必须是 HIR", no `DAGNode` straight into `ParseOutcome`).
§4.1 quantifies what that cost when this document was written: of the SMT-LIB logics, the HIR
could carry **QF_LIA, QF_LRA, QF_LIRA and their quantifier-free Boolean fragments**, and
nothing else — not QF_BV, not QF_AUFLIA, not QF_S, not anything with an array or an
uninterpreted function. **That measurement is now out of date in the direction of good news**;
the table above states what is carried today and what is not.

The consequence for Plan 2 is unchanged in kind and much smaller in degree: **the baseline arm
still cannot route the whole corpus through the HIR**, but the fragment that has to be
excluded is now exactly the datatype, set, sequence and bag logics rather than everything
except linear arithmetic. §4.2's two options stand, and the honest one — translate what the
HIR carries and report the excluded fragment by name — is now a small exclusion rather than a
large one.

---

## 1. What the format is

SMT-LIB 2 is the standard input language of SMT solvers: a command script declaring sorts
and symbols, asserting formulas, and asking `check-sat`. It is this project's *target*
language, its baseline *source* language, and the reason the project exists in the shape it
does.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| The SMT-LIB Standard, Version 2.6 (Barrett, Fontaine, Tinelli) | 2.6 is the widely-implemented release; a 2.7 revision exists — **the exact target version was not re-confirmed in this pass** | <https://smtlib.cs.uiowa.edu/> |
| Theory declarations (Core, Ints, Reals, ArraysEx, FixedSizeBitVectors, FloatingPoint, Strings, …) | per-theory | same |
| Logic declarations (QF_LIA, QF_BV, AUFLIRA, …) | per-logic | same |
| SMT-COMP | the competition and corpus | <https://smt-comp.github.io/> |

The `Ints` theory declaration is the one this project has already had to read closely. Its
axiom, verified against the standard on 2026-08-12:

```
(forall ((m Int) (n Int))
  (=> (distinct n 0)
      (let ((q (div m n)) (r (mod m n)))
        (and (= m (+ (* n q) r))
             (<= 0 r (- (abs n) 1))))))
```

Those are exactly the two laws `test/regression/test_int_div_mod_semantics.cpp` asserts.
The theory's own note adds the reading: when `n` is positive `div` floors, and when `n` is
negative it *ceils* — which is why floor division is not SMT-LIB's convention but only its
restriction to positive divisors, and is plausibly how this engine's `div` and `mod` drifted
apart (`minizinc.md` §4.1). The axiom is guarded by `n ≠ 0`, so division by zero is
unconstrained rather than erroneous, which is why folding it is wrong and leaving the term
symbolic is right.

### Reference implementations and corpus

cvc5 and Z3 are the reference implementations; SMT-COMP publishes per-division benchmark
archives and rankings. **Versions, instance counts and licence terms not re-confirmed in
this pass**, the same open item `docs/languages-scoping.md` §1.7 records for TPTP.

---

## 2. Semantics — what a file means

### 2.1 Commands

`set-logic`, `set-option`, `set-info`, `declare-sort`, `define-sort`, `declare-fun`,
`declare-const`, `define-fun`, `define-fun-rec`, `define-funs-rec`, `assert`, `check-sat`,
`check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`, `push`, `pop`, `reset`,
`exit`.

This project's parser implements them in `src/frontend/base_parser.cpp`, plus OMT extensions
(`minimize`, `maximize`, `assert-soft`, `lex-optimize`, `pareto-optimize`) in
`src/frontend/opt_parser.cpp`.

### 2.2 Sorts and symbols

`Bool`, `Int`, `Real`, `(_ BitVec n)`, `(Array I E)`, `(_ FloatingPoint e s)`, `String`,
`RoundingMode`, plus user sorts from `declare-sort` and abbreviations from `define-sort`.

`(set-logic L)` restricts what may follow. It is an assertion the file makes *about itself*,
and it is metadata rather than a constraint — but a benchmark's logic is how SMT-COMP
divides its corpus, so losing it makes a result unattributable to a division.

### 2.3 Terms

Applications, `let`, `forall`, `exists`, `ite`, `!` annotations (`:named`, `:pattern`),
and the theory operators. `define-fun` is a macro; `define-fun-rec` and `define-funs-rec`
are recursive definitions, and the latter is a *group* whose members may reference each
other — which is why `dumpSMT2` has to emit the group as one command, a defect fixed on the
`harden-dump-roundtrip` branch (`0ae8320`).

### 2.4 What a solution is

`sat` with an optional model, `unsat` with an optional proof or unsat core, or `unknown`.
Under the OMT extensions, an optimum as well.

---

## 3. Why this frontend must still go through the HIR

`docs/superpowers/specs/2026-08-10-languages-design.md` §6.1 rule 3 states it: a frontend's
product must be HIR, and putting a `DAGNode` straight into `ParseOutcome` is forbidden
because "违反此规则等于把编码决策散回 22 个前端". The rule is right, and this document does
not argue against it. It argues that **the rule has a cost here that it does not have
anywhere else**, and that the cost must be measured before the baseline arm is built on it.

For every other language, the HIR is a *wider* target than the source needs — the source has
`alldifferent`, the HIR has conjunctions, and the encoding choice is the interesting part.
For SMT-LIB 2, the source *is* the target, and the HIR is a narrowing in the middle.

| | other 21 languages | SMT-LIB 2 |
|---|---|---|
| source → HIR | may lose (an encoding choice, recorded as `Fidelity`) | **loses, with nothing to record it** |
| HIR → Parser | exact | exact |
| what the HIR adds | one representation, shared passes, recorded choices | nothing the source did not have |

---

## 4. Semantic gaps and encoding choices

### 4.1 What the HIR cannot carry, measured

**Re-measured 2026-08-14, when the baseline was implemented.** The table this section used to
carry was written on 2026-08-12 and every row of it is now wrong: it said the HIR had no
bit-vectors, no strings, no arrays, no quantifiers, no uninterpreted functions and no real
literal. All of those landed between then and now. The figures below are produced by running
`languages/smtlib2` over `test/instances` and counting what refused, so they can be
rechecked rather than believed.

| | |
|---|--:|
| instances under `test/instances` | 21 |
| translated | **16** |
| refused, by construct | 5 |

It was 10 of 21 on 2026-08-15, and what the shortfall turned out to be is worth
recording, because none of it was a missing *feature*: two whole clusters of
operators existed in the HIR and were simply absent from the lift table, and one
more could not be a table entry at all.

| What refused | Instances | Why the HIR cannot carry it |
|---|--:|---|
| algebraic datatypes | 1 | no `SortKind::DATATYPE` constructors reach the lift |
| real algebraic numbers (`root-obj`) | 1 | no HIR literal for them |
| `str.indexof_re` and the other regex-string operators | 1 | `STR_INDEXOF_RE`, `STR_REPLACE_RE`, `STR_REPLACE_ALL_RE` have no `Hir::Op` |
| constant arrays (`(as const (Array …))`) | 1 | no HIR operator |
| FP constants in bit-representation form (`(fp #b0 #b1000 #b0…)`) | 1 | `LIT_FLOAT` carries decimal text, and the three-bit-vector form is exact where a decimal is not |

| What stopped refusing, and why it had | Was |
|---|---|
| `define-fun`, `define-fun-rec` | the definition crosses as an **axiom**, `forall x. f(x) = body` — which is what SMT-LIB says a define-fun *means*. The old entry said the HIR has no body-carrying function; true, and it turned out not to matter. The axiom form is also the only one that expresses `define-fun-rec`, since an inliner cannot terminate on one. |
| `let` | **inlined**. SMT-LIB defines `let` by substitution, so this is exact; it costs size and not meaning. Before, a let-bound reference lifted as an `IDENT` the model never declares. |
| the regular expressions | every operator already existed in the HIR and none was in the lift table |
| `(_ extract hi lo)`, `zero_extend`, `sign_extend`, `(_ re.loop i j)` | **indexed** operators, which cannot be table entries: the engine stores indices as ordinary constant *children* and the HIR keeps them in `Expr::indices`, so the lift has to move one into the other |
| `(_ int2bv w)`, `(_ fp.to_sbv w)`, `(_ fp.to_ubv w)` | indexed too, and differently again — the width is in the **result sort** rather than in a child, so each needs its own branch |
| `re.none`, `re.all`, `re.allchar`, `(as set.empty …)` | nullary, so they are HIR *literals* rather than operators (`mkOp` refuses an empty argument list) and cannot be table entries either |
| `ubv_to_int`, `sbv_to_int` | unsigned and signed bit-vector conversion, respectively. Source `bv2int` is the unsigned solver alias, like `bv2nat`; signed internal HIR `BV_TO_INT` emits `sbv_to_int`. |
| `(Tuple …)`, `UnitTuple` and the five tuple operators | the **sort** was missing, not the operators — §4.6 |

What the baseline **does** carry, each with a case in `test/languages/test_smtlib2.cpp`:
Bool and linear integer arithmetic, all three integer-division conventions, real arithmetic
and real literals, bit-vectors including the signed/unsigned orderings, arrays with `select`
and `store`, uninterpreted sorts and functions, quantifiers with shadowing handled by
alpha-renaming, strings, sets, and floating-point sorts and arithmetic.

So the fragment is no longer "QF_LIA and its sub-fragments". It is most of the quantified and
quantifier-free logics over the standard theories, with datatypes as the largest remaining
hole — which is the one SMT-COMP division this arm still cannot enter.

**The gap that matters is no longer size but silence**, and that is what the frontend is
built around: an unliftable construct refuses the whole instance rather than translating a
smaller one. A missing instance is a visible gap in a results table. A silently smaller
instance is a wrong row.

### 4.2 The two honest options

| Option | What it means | Cost | Honest? |
|---|---|---|---|
| **A. Bypass the HIR for the baseline only** | `parse()` straight into a `Parser`; the baseline arm is a round-trip self-test and a timing reference, not a `translate()` client | violates design spec §6.1 rule 3 — so the rule needs an explicit, documented exception rather than a quiet one | yes, if written down |
| **B. Grow the HIR until it carries the logics being measured** | bit-vectors, arrays, UF, quantifiers — clusters C, F, G and more | large, and mostly *not* otherwise needed: BTOR2 and CryptoLine want bit-vectors (`docs/languages-scoping.md` §3.1 cluster F), TPTP and Boogie want UF, but nothing else in the batch wants strings or floating point | yes |
| C. Restrict the baseline corpus to QF_LIA and report it as "SMT-LIB" | — | zero | **no** |

**Decided 2026-08-12: B.** SMT-LIB is to be supported in full rather than as the fragment
the HIR happens to carry, and design spec §6.1 rule 3 stands with no exception. The bill and
its sequencing are in `docs/hir-design-decisions-2026-08-12.md` §2; option C is explicitly
ruled out. The recommendation below is retained because the reasoning against A is what
made the decision worth asking for.

~~**Recommendation: A now, B incrementally.**~~ The baseline arm's job is to answer "how fast is
the solver on the benchmark in its native form", which needs no HIR at all — and the
round-trip property that makes it trustworthy is already being built independently on the
`harden-dump-roundtrip` branch (§4.4). Option B follows the other languages: bit-vectors
arrive with BTOR2, UF with TPTP, quantifiers with QDIMACS, each paying for itself.

What must **not** happen is option C by default, which is what happens if nobody decides:
the frontend gets written, it refuses everything outside QF_LIA with
`E_UNSUPPORTED_CONSTRUCT`, the coverage number looks like a language-coverage problem, and
the baseline silently becomes a fragment.

### 4.3 If the lifting is built, what it looks like

`SmtToHir` — the design spec's name for it — is a `DAGNode` → `Hir::Expr` walk. Three notes
for whoever writes it:

- **It is a lowering, not a parse.** The parse already happened; this converts one IR to
  another. Its failure mode is `E_UNSUPPORTED_CONSTRUCT` naming the `NODE_KIND` it met, so
  the coverage statistic reads as "the HIR does not carry this", which is true, rather than
  "SMT-LIB has a construct we cannot parse", which is false.
- **Hash-consing does not survive.** `DAGNode`s are interned (`CLAUDE.md` invariant 1); a
  naive walk rebuilds shared subterms once per occurrence and can blow up exponentially on a
  DAG that was linear. Memoise on `DAGNode` identity.
- **`define-fun` must be inlined or dropped deliberately.** The HIR has no function
  definition; inlining is exact but can multiply size, and dropping a *used* definition is
  a wrong model.

### 4.4 The round-trip property, and why it belongs here

This is the one language whose translation is checkable against itself:

```
parse → dumpSMT2 → parse → dumpSMT2      must be a fixed point
```

That property is being hardened on branch `harden-dump-roundtrip`, which found three defects
the hand-written test could not: `define-funs-rec` emitted as separate commands whose bodies
forward-reference each other (`0ae8320`), `NT_STR_INDEXOF_REG` printed under another
operator's name (`c90cffb`), and commutative operands reordered on re-entry so the dump did
not converge (`3316308`, `fffe0d5`).

All three were found by running the property **over the real instance corpus** rather than
over cases somebody thought to write down (`33908e5`). That is the same lesson
`docs/known-defects-2026-08-11.md` §4 draws about checks that cannot fail, arriving from the
other direction: a test whose input is hand-picked can only find what its author already
suspected.

For the baseline arm this property *is* the validation. There is no differential oracle
needed — the format's own re-readability is the invariant.

### 4.5 OMT is an extension, and the dialects disagree

This project's parser accepts `minimize`/`maximize`/`assert-soft`/`lex-optimize`/
`pareto-optimize`, and `Lower::OmtDialect` emits three different renderings
(`include/somtparser/lowering/omt_emitter.h`). None of this is standard SMT-LIB 2: the
SMT 2025 proposal (`define-objective`/`optimize-sat`) is not implemented by any solver yet,
Z3 uses `(minimize t)`, OptiMathSAT its own.

**Multi-objective combinations** landed for the 2025 dialect on 2026-09-20, against Fig. 1
of the proposal as transcribed in `docs/related-work-round2.md`:
`(define-multi-objective ⟨symbol⟩ ⟨m-objective-kind⟩ ⟨symbol⟩+)` over
`OBJECTIVE_LEX | OBJECTIVE_PARETO | OBJECTIVE_BOX | OBJECTIVE_MINMAX | OBJECTIVE_MAXMIN`.
The declaration names its members, so it is emitted *after* them and followed by a single
`optimize-sat` on the multi-objective symbol — one per member would request several
independent optimisations, which is `OBJECTIVE_BOX` and a different problem. Note the
asymmetry: the proposal covers `MINMAX`/`MAXMIN`, which have no Z3 rendering at all, so
**the dialect nobody implements yet is the more expressive one** — which is the argument
for emitting it. The current emitter also implements OptiMathSAT's supported
multi-objective modes; see [the current dialect contract](../translation-output.md).

Consequence for a baseline arm that reads OMT benchmarks: **the source dialect is part of
the benchmark's identity**, and a translation between dialects is a real transformation even
though it looks like formatting. `Parser::parseAny` already relies on this — it moves content
between two in-process `Parser`s via `Translation::toParserSmt2()`, which preserves
native theories for internal replay (`src/frontend/base_parser.cpp:4662`). The current parser
also reads the supported GOMT objective forms described in the dialect contract.

---

### 4.6 Tuples — the set gap, one theory over

Three corpus files refused with `sort '(Tuple Int Bool)' has no HIR counterpart`, and the
shape of that message is the interesting part: it names a *sort*, and the table above is a
table of operators. The engine had the whole theory — `SORT_KIND::SK_TUPLE`, five
`NODE_KIND`s, `oper_key_map` entries, `createTupleSort`, five builders each with its own
index range check, and a printer that knows `((_ tuple.select i) t)` writes its index inside
the operator. `ParserToHir::liftSort` had no line for it. So every such script failed at its
**declaration** and not one of the five operators was ever reached.

This is the set row of §4.4's round-trip discussion repeating exactly, and it is the failure
mode `CLAUDE.md` §6 ranks as the one an enum diff cannot find: an operator table is only as
reachable as the sort table under it.

**Implemented 2026-09-22.** `SortKind::TUPLE` keeps the field sorts in `Sort::args` — the
field a parametric datatype already uses, for the same reason: a vector of sorts that makes
a `Sort` recursive without making it large. Four points where the obvious thing is wrong:

* **a tuple sort is created, never resolved.** It is structural, not declared: `(Tuple Int
  Bool)` means the same thing in two files that never heard of each other, so `lowerSort`
  calls `createTupleSort` where the datatype case has to look a declaration up. Nothing is
  emitted for it, because a script does not declare one.
* **`UnitTuple` is a sort, not a malformed tuple.** The nullary tuple has exactly one value
  and its own SMT-LIB spelling. Four separate emptiness checks — in the lift, in
  `sameSort`, in `toString` and in the checker — have to agree about that, and an "a tuple
  needs fields" guard in any one of them would refuse a conforming script.
* **three of the five are indexed**, so they are not lift-table entries, for the reason
  `(_ extract hi lo)` is not. The engine spells an index as a constant *child* and the HIR
  keeps it in `Expr::indices`. The three do not agree on which children are indices:
  `tuple.select` is `(t, i)`, `tuple.project` is `(t, i₁ … i_k)`, and `tuple.update` is
  `(t, i, v)` — the index sits **between** the two terms, so a loop that took everything
  after the first child as indices would turn the replacement value into an index.
* **`tuple.unit` is a literal**, like `re.none` and `(as set.empty …)`, because `mkOp`
  refuses an empty argument list. Unlike `set.empty` it needs no sort annotation: `UnitTuple`
  is the only sort it can have.

Pinned by `test/hir/test_uir_tuples.cpp` and by eleven rows in the operator sweep. The sweep's
tuple prelude is `(Tuple Int Bool)` rather than `(Tuple Int Int)` on purpose — with two
fields of one sort, a lift that dropped the index or read the wrong field still type-checks.

---

### 4.7 Reference audit of the last four cases

After §4.6 the corpus stands at 44 of 48. The four that remain were carried as
"1 open gap + 3 extensions (D26)", and running cvc5 1.4.0 over them moves two of
the four and confirms a third. The rule being applied is the project's own: *a
refusal whose stated reason is "we do not know what the reference implementation
does" is not an open question, it is an unrun experiment.*

| File | cvc5 1.4.0 | What it is |
|---|---|---|
| `datatypes_cdt-enum-type-mismatch.smt2` | `sat` | native coinductive declarations carried through HIR — see below |
| `datatypes_nullable_checks.smt2` | `(error "Parse Error: … nullable.some requires exactly one argument.")` | **cvc5's own NEGATIVE test** — its header says `; EXIT: 1` and `; EXPECT: (error "Parse Error:`. SOMTParser reports `E_PARSE` for this known arity error. A unary `nullable.some` application remains unsupported; nullable semantics are not implemented. |
| `sets_set_is_empty.smt2` | `unsat` | now translated with `cvc5_sets=1` (§8) |
| `sets_proj-issue632.smt2` | `sat` | now translated with `cvc5_sets=1`; the bare empty set defaults to `Set Bool`, and query assumptions are preserved (§8) |

**`declare-codatatypes` is not `declare-datatypes` with another keyword.** A
codatatype is coinductive: its values may be infinite, and that is the entire
difference. The corpus file declares `S = A(a: S)`, which has **no finite
values**, so:

```
(declare-codatatypes ((S 0)) (((A (a S)))))  (declare-fun y () S) (check-sat)
    cvc5 1.4.0 -> sat            -- inhabited by exactly one infinite value
(declare-datatypes   ((S 0)) (((A (a S)))))  (declare-fun y () S) (check-sat)
    cvc5 1.4.0 -> (error "Parse Error: Datatype sort S is not well-founded")
```

So reading a codatatype as a datatype is not a weaker answer or a recorded
approximation — it is a declaration a conforming solver **rejects**. There is no
under- or over-approximation to record a `Fidelity` for, because there is no
translation. The earlier claim that
`declare-codatatypes` is defined by SMT-LIB 2.6 was incorrect; this is cvc5's
coinductive extension, documented in its
[datatype theory reference](https://cvc5.github.io/docs/cvc5-1.3.0/theories/datatypes.html#codatatypes).

A closed-product singleton encoding was prototyped on 2026-09-22, but was not
accepted: constructor disequality produced a reference/target discrepancy, and
reference model checking timed out. That prototype was discarded.

The implementation now stores `coinductive` on engine sorts and HIR datatype
declarations. Both lowering directions preserve it. Dumping uses the dependency
SCCs to emit `declare-codatatypes` for corecursive groups and `declare-datatypes`
for inductive groups; a mixed recursive SCC is refused. Parametric declarations,
constructors, selectors and testers retain their existing typed representation.
The command log exposes `DECLARE_CODATATYPES` separately, and the translation
report records `native-coinductive-declarations` and its solver requirement.

This is native preservation of cvc5's extension, not a finite encoding for solvers
without it. The regression tests compare original queries and two HIR round trips
using cvc5, including an infinite cyclic stream that is SAT as a codatatype and
UNSAT with the corresponding inductive datatype declaration.

---

## 5. New HIR surface this format forces

Everything the other twenty-one documents propose, plus the theories none of them need:

| Surface | Needed for | Also wanted by |
|---|---|---|
| `SortKind::BITVEC` + bit-vector operators + `ExprKind::LIT_BITVEC` | QF_BV, QF_ABV — SMT-COMP's largest divisions | BTOR2, CryptoLine (cluster F) |
| `SortKind::ARRAY` + select/store | QF_A*, and the batch's array languages want a *different* array (index sets, `essence-prime.md` §4.4) | MiniZinc, FlatZinc, XCSP3, Essence′ |
| `ExprKind::APPLY` + `SortKind::UNINTERPRETED` | QF_UF* | TPTP, Boogie (cluster G) |
| `ExprKind::FORALL` / `EXISTS` | the quantified logics | QDIMACS, TPTP (cluster C) |
| ~~`ExprKind::LIT_REAL`~~ **landed 2026-08-12** | QF_LRA, QF_NRA | LP, MPS, MiniZinc |
| `SortKind::FLOAT`, `SortKind::STRING`, `ExprKind::LIT_STRING` | QF_FP, QF_S | **nothing else in the batch** |
| `ExprKind::LET` | `let` bindings; inlining is exact but can blow up | — |

The last two rows are the reason option B in §4.2 is "incrementally" and not "first": 88 of
the engine's kinds are floating point and strings, wanted by no other language, and building
them into the HIR to support a baseline that could instead bypass the HIR entirely would be
the most expensive way to buy the least.

---

## 6. Fidelity summary

**Exact — the whole format, via the direct path** (`Parser::parse`). This is the native
frontend; there is no translation and no loss.

**Exact — QF_LIA and sub-fragments, via the HIR.** Booleans, integers within `long long`,
the eleven `Hir::Op` operators, and assertions.

**Blocked, not lossy, via the HIR** — and this is the finding: every other logic.
Bit-vectors, arrays, uninterpreted functions, quantifiers, floating point, strings, and real
literals are `E_UNSUPPORTED_CONSTRUCT` at the lifting step. That is honest per instance and
**dishonest in aggregate** if the resulting corpus is still called "SMT-LIB" (§4.1).

**Inherently lossy: nothing**, in either path. The gaps are representational, not
approximative — there is no encoding choice to make and no `Bound` to record.

**Ways to make it wrong by mistake**:

- Building the baseline arm on the HIR and reporting the surviving fragment as "SMT-LIB"
  (§4.1, §4.2 option C). **The corpus is replaced, not the question.**
- Rebuilding a hash-consed DAG naively during lifting (§4.3). Exponential blow-up on inputs
  that were linear.
- Dropping a `define-fun` that is used, or inlining one without bounding the growth (§4.3).
- Treating an OMT dialect change as formatting (§4.5).
- Losing `(set-logic …)`, which makes a result unattributable to an SMT-COMP division
  (§2.2).

---

## 7. References

**Standard**

1. C. Barrett, P. Fontaine, C. Tinelli, *The SMT-LIB Standard, Version 2.6*.
   <https://smtlib.cs.uiowa.edu/> — **target version not re-confirmed in this pass**.
2. SMT-LIB theory declarations, in particular `Ints` (the `div`/`mod` definition
   `minizinc.md` §4.1 and `test/regression/test_int_div_mod_semantics.cpp` depend on).
3. SMT-COMP. <https://smt-comp.github.io/> — divisions, benchmark archives and rankings.
   Instance counts and licence terms **not re-confirmed**.

**This project**

4. `docs/superpowers/specs/2026-08-10-languages-design.md` §6.1 rule 3 (the HIR-only rule
   §3 and §4.2 discuss), §4.7 (HIR).
5. `docs/languages-scoping.md` §3.1 (cluster J, and clusters C/F/G this document draws on),
   §3.2 (0.2×), §6 (the second filter §4.1 fails in an unusual way), §4 (Plan 2).
6. `docs/languages/qdimacs.md` §5 (cluster C), `docs/languages/tptp.md` §5 (cluster G),
   `docs/languages/btor2.md` §5 (cluster F), `docs/languages/lp.md` §4.1 (the real literal),
   `docs/languages/essence-prime.md` §4.4 (why the batch's array want differs from
   SMT-LIB's).
7. `docs/languages/minizinc.md` §4.1 (how the `Ints` `div`/`mod` definition was checked
   against this engine, and what it found).
8. `docs/known-defects-2026-08-11.md` §4 (the hand-picked-input lesson §4.4 echoes).
9. Branch `harden-dump-roundtrip`: `33908e5`, `c90cffb`, `0ae8320`, `3316308`, `fffe0d5`.
10. `include/somtparser/core/kind.h`, `include/somtparser/hir/hir.h`,
    `include/somtparser/lowering/omt_emitter.h`, `src/frontend/base_parser.cpp`,
    `src/frontend/opt_parser.cpp`, `test/regression/test_int_div_mod_semantics.cpp`.

## Numeric optimization through the HIR adapter

The baseline adapter preserves plain Int/Real `minimize` and `maximize`
objectives. Several objectives require `(set-option :opt.priority lex)`;
otherwise it refuses the input rather than choosing an objective order.
Other priorities, grouped objective commands and custom
comparison/epsilon/M modifiers currently produce unsupported-construct
diagnostics. The engine parser has broader OMT syntax support than this
adapter. This distinction prevents an accepted optimization script from
silently becoming a feasibility query. See `test_smtlib2_objectives` and the
`instances/ok` / `instances/reject` examples.

Constant numeric objectives, including the parser's initially polymorphic
integer numerals, are lifted as numeric HIR terms. A zero-cost MPS objective
therefore survives an SMT round trip instead of failing on `minimize 0`.

The adapter also preserves `assert-soft` for a single cost group with exact
positive integer weights. The decimal weight text is retained at arbitrary
precision. Multiple soft groups, mixed soft/explicit objectives, non-lexicographic
priority, and non-positive or fractional soft weights remain explicit refusals;
their objective order or weight domain is not silently approximated. The HIR
already carried soft constraints, but the SMT reader previously refused to
read back the WCNF frontend's output. See
`test/python/test_smtlib2_optimization_roundtrip.py` for feasible-set and cost
equivalence checks across two round trips.

## 8. Optional cvc5 finite-set compatibility

Pass `--opt cvc5_sets=1` to accept `set.is_empty X` by the exact finite-set
identity `card(X)=0`. A bare `set.empty` is explicitly ascribed `(Set Bool)`,
matching cvc5 1.4's default; it does **not** infer an integer/real set from a
sibling operand. Other element sorts need an explicit `as` ascription. Native
typing still rejects incompatible operands. Quoted symbols, strings and
declarations are not rewritten. Rewrites appear in the report as
`typed-set-identities`. This option is enabled explicitly by the three corpus
instruments for cvc5's own corpus; the default stays strict. The normalizer
has syntax-depth and node-count budgets.

A single terminal `check-sat-assuming` now contributes its assumptions to the
relational model. Previously the assertions could survive while its query
assumptions were dropped. Multiple assumption queries or later context changes
are refused pending explicit query selection. Tests compare source and output
with cvc5, including a case that becomes SAT if its assumption is omitted.

Source contract: [cvc5 finite sets](https://cvc5.github.io/docs/cvc5-1.3.1/theories/sets-and-relations.html).
