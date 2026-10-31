# MiniZinc — constraint modelling

**Reading this document (2026-10-01):** the dated tables and corpus counts below
are historical research notes, not a current language-conformance score.
Submission status identifies the qualified source
and competition cohort. The R190/R198 evidence
records a subsequently detected Boolean-index regression in an unpromoted
candidate. Scalar definedness, array construction and library-global
preconditions must be checked separately; Section 4.2 states the scalar rule's
scope.

**Implementation update, 2026-10-04:** typed JSON records, record arrays and
finite scalar/record lists now bind fields by name and preserve their declared
types and index order. Scalar and record functions evaluate in their definition
environment with fresh call-local binders. Filtered record comprehensions can
be indexed, including inside included function bodies. Recursive calls with
finite expansion are supported; exceeding the expression-depth limit fails
translation without emitting a truncated body. Array function signatures,
list-returning functions and `test` items remain unsupported. The exact source
passed 174 native/documentation checks and 3222 Python checks (one skip);
qualification receipts
separate these checks from the still-running 100-instance official replay.

Subsequent implementation supports finite scalar-array comparisons and
`arg_max`/`arg_min` over numeric or Boolean arrays and finite generators.
Comparisons retain source index sets and element definedness; extrema preserve
the least source index on ties, including enum indices.

The current implementation also resolves forward scalar functions across
included files and accepts finite array function parameters. Parameter domains
contribute to each call's definedness, including when the call is negated.
Array argument types are checked even when empty; Boolean arguments can coerce
to numeric element types. Computed finite scalar arrays support dynamic indexing
with bounds and element-definedness guards. Fixed set-array reads, equality,
subset and set operations can be evaluated in parameter expressions and `test`
bodies. Fixed set-returning functions accept finite set arguments, including
empty sets, and check declared element domains and nominal enum identity.
Type variables unify across scalar, set and finite-array parameters. Finite
recursive set helpers expand in their definition environment; library `test`
overloads and decision-variable predicates retain distinct dispatch paths.
List-returning functions remain unsupported. These frontend capabilities do not imply that all official
competition instances translate or that every exported model has been proved
equivalent to its source.

Finite scalar comprehensions over fixed generators can also produce optional
Bool, Int and Real cells when a `where` clause depends on decision variables.
Parameter-only false conjuncts filter generator tuples first; remaining cells
retain separate occurrence and definedness. Supported consumers include
`occurs`, `absent`, `default`, numeric sums/products, Boolean folds, array
indexing/reindexing/concatenation, equality and integer `all_different`.
Declarations of arbitrary `var opt` values and optional compound values are
outside this fragment.

For these computed decision-optional cells, the verified `deopt` contract
requires that the cell occurs. Models must establish this precondition at the
use site; use `default` when absence is possible. The
[MiniZinc 2.9.4 library reference](https://docs.minizinc.dev/en/2.9.4/lib-stdlib-optiontypes.html#deopt)
distinguishes this contract from fixed optional parameters, whose absent
`deopt` is undefined. Unguarded absent `deopt` can expose compiler-specific
hidden values: the retained 2.9.4/Gecode partial-head probe returns SAT where
this frontend's partial-value encoding returns UNSAT. That result is a known
profile difference, not a successful equivalence check or a generic zero-value
rule. Qualification records all 33 probes, including this difference; guarded
uses and the other supported consumers are assessed separately.

Local fixed `list of Record` bindings preserve structural field types and outer
bindings, including empty comprehensions. Finite comprehensions accept alias
clauses such as `p = 2*i` before dependent generators. Grouped set membership
keeps fixed intervals compact and preserves operand definedness. Predicate
type variables unify integer element and index positions; user function and
predicate calls accept a trailing argument comma.

Finite `forall` and `exists` generators expand over the exact source binding
sets without a cardinality threshold that changes them into SMT quantifiers.
This includes domain holes, empty domains, dependent generators, aliases,
filters and reified uses. Undefined Boolean cells close separately inside each
binding. The resulting finite Boolean constraints can be used by ordinary OMT
without residual generator quantifiers. Conversion size and resource use for
large products are measured on the current exported instances.

Historical result: an earlier isolated candidate kept large independent
primitive generators quantified. Official skill-allocation case 78 changed
from `bad_alloc` with no target to complete conversion and full Z3 Optimize
parsing under that experiment's original 1 GiB, 120-second CPU and 300-second
wall budgets. That candidate used `-O1`, while its baseline used Release flags.
This retained record establishes that earlier conversion result; it does not
measure the current expansion path or establish a compiler-independent speedup.

Predicate and function parameter declarations also accept a trailing comma.
Generators over parameter arrays of sets bind each complete set cell, retain
duplicate cells, and restore enclosing bindings. `floor`/`ceil` of `log2(n)`
or `log(b,n)` use exact integer-power comparisons for fixed integer operands
accepted by the parameter evaluator (`b > 1`, `n >= 1`). General real-valued
logarithms remain unsupported.

`abs` accepts integer and real expressions, including implicit Boolean and enum
coercions. Fixed arguments can be used in parameter arrays, index sets and
rounding expressions. Decision expressions use the shared HIR absolute-value
operator and retain operand definedness under Boolean negation. Integer
parameter folding diagnoses overflow rather than wrapping.

In finite-array contexts, fixed integer and enum ranges coerce to ordered arrays
indexed from 1. This includes ranges passed to `reverse`, `sort` and `array1d`;
explicit constructors can subsequently reindex them. Bounds must be fixed and
defined, and the resulting initializer must still match its declared shape.

Fixed set arrays also accept `array1d` through `array6d` constructors and
one-dimensional concatenation. The frontend preserves index origins, enum
identity and compact interval sets, and checks constructor shapes against cell
counts. Fixed-set algebra is accepted in generator domains; Boolean `xor` and
integer range membership with variable endpoints retain operand definedness.
Finite-domain decision-set arrays also preserve each cell's element domain.
For integer carriers with at most 65,536 members, the frontend constructs the
exact finite set `D` and encodes the domain as `S intersect D = S`. This excludes
all elements outside `D`, including holes, without an explicit quantifier.
Equality between finite set-array slices and fixed arrays uses complete set
equality, including absent elements; cardinality lowering retains the same
proven carrier. Larger interval carriers retain the exact quantified membership
encoding, so the frontend does not claim quantifier-free output for every model. Local decision arrays may have multiple
index axes, and array-valued record fields retain their finite shape through
comprehensions.

Numeric array initializers preserve their index origins: ordinary lists and
comprehensions use `1..length`, while `arrayNd` supplies explicit axes. A
mismatching declaration is rejected. Inferred `array[int]` declarations acquire
the initializer's axes. Enum-indexed positional values and JSON data without
index origins retain their declaration context.

`dom` accepts integer and enum expressions with proven finite bounds, including
actual function arguments and defined integer arithmetic. It returns a fixed
interval superset without constraint propagation. Argument definedness is
preserved; a fixed parameter context requires a known-defined argument, and an
unbounded argument is reported as unsupported instead of receiving invented
integer limits.

For a cell of a decision-set array with a known finite declaration domain,
`ub` uses that domain as a safe upper bound. It does not run constraint
propagation before evaluating the bound. MiniZinc permits different bounds
depending on evaluation context and preprocessing; models that inspect the exact
bound can therefore differ from a particular MiniZinc compiler's result.
See the [bound and domain specification](https://docs.minizinc.org/en/stable/spec.html#bound-and-domain-operations).

`connected` and `dconnected` accept four finite one-dimensional arrays with
fixed endpoints and Boolean node/edge selections. Edge arrays must have the
same index set; endpoint types and values must match the node index set.
The shared HIR encoding keeps an existential root/rank witness inside the
relation, including under negation. Directed connectivity means that some
selected root reaches every selected node, and selected edges require both
endpoints selected. The empty selected subgraph is false.

**Implementation update, 2026-09-29:** fixed arrays of integer sets now accept
finite parameter comprehensions, including nested set comprehensions and
multiple generator axes. Values populate the declared index range in ordinal
order; filtered cardinality and sparse element domains are checked. Integer
set generators are sorted and deduplicated consistently with named sets, and
nested binders restore their enclosing binding. Empty heads still use a
nominal constant binding for validation; a value-dependent undefined head may
therefore be refused even when the generator is empty.

Fixed Int, Bool and String parameter arrays now accept decision-valued indices
using finite HIR conditionals. Mixed fixed and dynamic matrix coordinates
select the relevant row or column. Decision-array initializers containing `_`
use the declared array so unconstrained cells remain unconstrained. All paths
retain index definedness at the enclosing Boolean scope, including under
negation; they do not turn an out-of-range access into an arbitrary value.
This dated description is not qualification of every Boolean consumer: the
R190/R198 regression and the qualified R205 repair must be assessed at their recorded
revisions. These frontend changes use existing HIR operators. Dynamic indexing of
set-valued cells remains a separate missing path. The official ATSP and TSPTW
replay is recorded separately from the historical coverage numbers below.

`concat` accepts one-dimensional finite arrays of strings, including parameter
comprehensions and enum-indexed arrays. It preserves element order and duplicates,
returns the empty string for an empty array, and retains definedness guards for
dynamic element selection. Undefined string values cannot become fixed parameters.
An explicit user function named `concat` retains its declared body.

**Date**: 2026-08-12
**Status**: format research for Plan 2 (`docs/languages-scoping.md` §4). The only language in
the batch with product code already in tree (`languages/minizinc/src/mzn_minimal.cpp`), which
this document is careful to describe as the skeleton it is.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster A, §3.2 (the **1.0× cost
baseline**, plus ~1.5× more to finish), §4 (Plan 2).

<!-- proposed-hir: Op::IFF, ExprKind::COMPREHENSION, ExprKind::ARRAY_ACCESS, SortKind::ENUM, SortKind::REAL_OPT -->
<!-- rejected-hir: Op::DIV, Op::MOD -->
<!-- The names above are HIR this format would force, not HIR that exists.
     scripts/check-doc-citations.py keeps the two apart: it fails if one of them
     is a typo, and it fails again once one of them actually lands, so this
     document cannot go on calling it future work. -->

**Headline result of the audit in §4**: MiniZinc is the cluster-A archetype and its cost is
in the type system, not the grammar — but the finding that matters most is smaller and
sharper than "arrays are hard". **MiniZinc's `div` and `mod` do not mean what SMT-LIB's
`div` and `mod` mean** (§4.1). Both languages spell them the same, both accept the same
operands, and the two disagree on every negative dividend. Nothing in the pipeline would
notice: no diagnostic, no `Fidelity` value, no failed round trip — just a different answer.
That is the single most dangerous construct in this document, and it costs one line of
code to get right and one line to get wrong.

The second finding is that MiniZinc's treatment of **partial functions** (§4.2) is a
deliberate, specified semantics rather than an omission, and it is *not* the semantics a
naive translation produces.


<!-- implicit-constraints:
  a partial function applied out of its domain (x div 0, a[i] with i out of range) => the enclosing Boolean context is FALSE, under MiniZinc's relational semantics; SMT-LIB's division is total and under-specified, so a direct mapping turns UNSAT into SAT (§4.2)
  `var 1..5: x` => VarDecl lower_bound and upper_bound, which are the declaration and not a separate constraint (§3.1)
  exactly one solve item => enforced at parse time; zero used to translate an empty model and exit 0, two used to become a two-objective OMT problem (§2.5)
  a constraint used in a Boolean context => reified; free in SMT, where a formula is a term of sort Bool (§4.6)
  `/* ... */` block comments do not nest => the first `*/` closes one, and an unterminated one is a TRUNCATED FILE rather than a short one (§2.1)
  a parameter is a compile-time constant => evaluated at parse time, because `array[1..n]` needs n's value and not a reference to it; an unbound one needs a .dzn and is refused (§2.2)
  `->` binds looser than a comparison => `b -> x <= 4` is `b -> (x <= 4)`; a chain is refused rather than given an assumed associativity (§2.4)
  annotations do not change the declarative semantics => `:: add_to_output`, `:: int_search(...)` are skipped, which the specification licenses and an `include` of a model file does not (§2.5)
-->
---

## 1. What the format is

MiniZinc is a solver-independent constraint modelling language: a user writes a model in
MiniZinc, and the toolchain *flattens* it to FlatZinc (see `flatzinc.md`), which is what a
solver actually reads. It is the input language of the MiniZinc Challenge and the de facto
standard modelling language of the CP community.

The two-level structure is the first thing to understand about it, because it decides what
this project is even measuring. Translating **MiniZinc** means making the encoding decisions
ourselves; translating **FlatZinc** means measuring someone else's. `flatzinc.md` §1 states
the same fact from the other side.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| The MiniZinc Handbook, including the language specification | **2.9.7** current as of 2026-08-12 (verified) | <https://docs.minizinc.dev/> |
| MiniZinc Challenge | annual; the corpus and the solver ranking | <https://www.minizinc.org/challenge/> |

The Handbook's specification chapter is a genuine specification — unusually good for this
batch, and much better than DIMACS's "suggested format" (`dimacs-cnf.md` §1) or LP's
vendor-dialect situation (`lp.md` §1). It defines the type system, the flattening
relation and, importantly for §4.2, the semantics of undefinedness.

**Pin the exact version before implementation.** MiniZinc is a moving language: tuples and
records arrived in the 2.8 series, and the global-constraint library grows between
releases. A document that says "MiniZinc" without a version is describing a moving target,
which is the mistake `docs/languages-scoping.md` §1.2 records for QDIMACS's solver choice.

### Reference implementation

`libminizinc` (MiniZinc 2.x, Monash University), which provides the `minizinc` driver and
the flattener historically called `mzn2fzn`. **Repository URL, licence and current release
were not re-confirmed in this pass**; pin them before differential testing, since the
flattener is also the natural oracle for checking a MiniZinc → HIR translation against a
MiniZinc → FlatZinc one.

### Corpus

The MiniZinc Challenge instance archives, one per year. `docs/languages-scoping.md` §7
records the Challenge as a competition with a corpus, a reference implementation and a
published baseline — it passes the first filter. It also passes the second (§6 there):
a MiniZinc model asks "is there an assignment satisfying these constraints, optimal for
this objective", which is the same question an SMT/OMT solver answers. No reinterpretation
is needed, unlike SyGuS-IF (`sygus-if.md` §4) or SYNTCOMP (`syntcomp.md` §4).

**Instance counts and licence terms: not re-confirmed in this pass**, the same open item
`docs/languages-scoping.md` §1.2 and §1.7 record for QBFLIB and TPTP.

---

## 2. Semantics — what a file means

### 2.1 Items

A MiniZinc model is a sequence of items, in any order. Order does not matter: a variable may
be used above its declaration, which is why `languages/minizinc/src/mzn_minimal.cpp` mints
objective names only after the whole model is parsed (§3.3 below).

| Item | Form | In the skeleton? |
|---|---|---|
| Include | `include "globals.mzn";` | standard-library name skipped; any other file refused |
| Variable declaration | `var int: x;` `var 1..5: y;` `var -10..10: z;` | int, bool and integer ranges, negative bounds included |
| Parameter declaration | `int: n = 3;` `par int: m = n*n;` | yes, evaluated at parse time (§2.2) |
| Assignment | `x = 3;` | no |
| Constraint | `constraint x > 2;` | yes |
| Solve | `solve satisfy;` `solve minimize x;` | yes, and exactly one is now required |
| Annotation | `:: add_to_output`, `solve :: int_search(...)` | parsed and skipped (§2.5) |
| Output | `output ["x = ", show(x)];` | parsed and skipped with a note (§2.5) — it constrains nothing |
| Predicate | `predicate p(var int: a) = a > 0;` | **read, and inlined at each call site** (§3.3) |
| test / function | `function var int: f(...) = ...;` | refused |
| Annotation declaration | `annotation my_ann;` | refused |
| Enum | `enum COLOUR = {RED, GREEN};` | refused |
| Type-inst synonym | `type Small = var 1..10;` | refused |

The frontend's `coverage_` (`languages/minizinc/src/mzn_minimal.cpp`) declares
19 of 21 targeted constructs supported. The table used to read 9 of 10, and what changed it
was running libminizinc's own `tests/spec/examples/` (`instances/upstream/`): **0 of 16
files translated, and every one failed at line 1, column 1**, on the `/* */` licence header
this lexer did not know. Six of the sixteen targets are constructs that corpus proved are
load-bearing and the table had simply not been counting — a subset measured against itself
reports full marks. Generator calls and parameter arrays landed on 2026-08-14; multi-file
`include`, `.dzn` data files and item-order independence on 2026-08-16, which is why the
last two are no longer listed as missing.

The corpus is **7 of 16**. It first moved from 2 to 5 on 2026-08-17 after three rounds
without a count change. Two changes did that: generator GROUPS
(`all_different(r, c in 1..n)(a[r, c])`, several variables over one index set), and
`output` items, which are now **skipped with a note** rather than refused. An `output` item
says how a solution is printed and constrains nothing, so skipping it is the same reading
annotations already get — and the three magicsq instances had been translating everything
above their output item for some time.

Before that it was **2 of 16**, and for one day it was two different numbers: 1 of 16 under
`default` against 2 of 16 under `ground`. The difference was not a frontend gap.
`queen_cp2.mzn` parsed and translated, and `default` then refused it with
`E_PASS_PIPELINE`, because its pipeline was empty and nothing eliminated the
`global-constraint` feature (§4.3) — the pass existed, was registered and was `exact()`.
A coverage table cannot see that: it reports on what the frontend read, and the refusal
happened a layer later. `default` and `strict` now run `decompose-globals` with the ground
style, so the corpus reads the same under all four non-bounding profiles.

**`var float` declarations and real division are implemented.** MiniZinc's
declarative float carrier is mapped to SMT `Real`; decimal, scientific and hexadecimal
constants are converted directly to exact rationals, and division by zero uses
the same relational definedness guard as integer division. Fixed float
parameters, float arrays, and `var float` predicate parameters use the same
representation. The concrete precision chosen by a MiniZinc solver remains an
implementation strategy rather than an invented SMT FloatingPoint format.

Finite list comprehensions used as decision-array initializers now expand in
source order, including dependent generators and `where` filters. Their
relational expressions retain definedness, and `array[int]` receives the exact
source index set `1..length`; this moved `golomb.mzn` into the translated corpus.
Fixed set comprehensions now also retain a canonical union of disjoint integer
intervals, so sparse value domains such as the squares in `perfsq2.mzn` become
exact membership constraints instead of widened bounds; that file accounts for
the seventh corpus success. A set comprehension and `union`/`intersect` are now
read where a *term* is expected too — in the operand position of `in` and
`subset`, and only there — by unrolling to their elements at parse time, which
is the same machinery the fixed-set path uses and is still not first-class HIR
support for collection values. Par `set of int:` items
and multi-dimensional index sets landed earlier, flattened row-major with the
decision recorded as an `EncodingChoice`. Named integer domains now work for
scalar variables, array elements and predicate parameters in both the fixed and
the `var` form — with the difference between them stated rather than blurred: a
fixed argument is a constant, so its membership is *checked* at the call and an
out-of-domain one refused; a `var` argument is an expression, so the set is
emitted as a **hard constraint narrowing it**. The Handbook does not settle
which of those a `var` parameter's domain means, so it was settled by running
MiniZinc 2.10.1: it accepts an out-of-domain argument and its flattener then
reports the model inconsistent, which makes the domain a constraint on the
actual rather than a type-inst requirement on the caller (D35 in
`docs/open-questions-2026-08-13.md`). The constraint is hard rather than
conjoined into the call because the narrowing is unconditional and would
otherwise invert under `not p(x)`. Array-valued
predicate parameters remain the other current gap.

The scalar `default` operator captures a partial left value and evaluates the
fallback only when needed. Its precedence is tighter than arithmetic; an
out-of-range scalar array read can therefore use `a[i] default 0` without
constraining `i` to the source array's index set. Fixed index failures are
captured only in that scope. Bool, Int, Real and String values use the typed
relational adapter. Fixed optional integer and enum array cells now retain
presence separately from their payload, including through dynamic indexing:
`<>` is absent, while `0` is present. `occurs`, `absent`, and `deopt` preserve
that distinction; `deopt` of an absent cell is partial and can use `default`.
This does not add decision-variable optional types or compound defaults.
See implementation and validation status.

The `regular(array, regexp)` overload accepts nonempty finite integer and enum
arrays. It compiles concatenation, alternation, grouping, character classes
(including ranges and negation), `.`, `*`, `+`, `?`, and bounded repetitions
into finite automaton acceptance. Enum literals in a pattern use the array's
enum type. Malformed patterns are diagnosed; undefined input cells retain
their partial-expression semantics, including under negation.

**`index_set` and the fixed-set folds `max`/`min`/`card` are implemented**, as
*parse-time values*. A set in this subset has no HIR term — `par_sets_` is read by
declarations and never by the expression grammar — so a set-valued expression denotes a
value the parser knows rather than a term. That is the point rather than a shortcut:
`max(index_set(x))` has to be a number before a declaration below it can use it as an
index bound, and `index_set(x) = {}` has to be a truth value before a conditional
guarded by it can fold (§4.7). `max`/`min` of an empty set is refused, since MiniZinc
leaves it undefined and a sentinel would be a number the source never wrote; `card` of
one is 0. `index_set` on a multi-dimensional array is refused by name — MiniZinc spells
those `index_set_1of2` and siblings, and answering with the flattened span would report
this frontend's internal representation as though the source had asked for it. `max(a, b)`/`min(a, b)` and numeric array reductions are now elaborated into
typed comparisons and value conditionals with strict operand domains. Fixed integer parameter arrays fold
from their supplied values. Decision-array reductions use a balanced tree,
with quadratic expanded SMT text and logarithmic depth. Empty-array extrema
remain undefined and are refused. See the numeric overload notes.

**Aggregation arguments and the `count` global are implemented.** An array literal
or comprehension may be an aggregation's direct argument — `sum([e | i in S])`,
`forall([a, b])` — which the handbook's aggregate sugar (§2.2) defines to be the same
expression as the generator form `sum(i in S)(e)`; the two share the unrolling and emit
byte-identical scripts. `count(x, y, c)` constrains `c` to be the number of elements of
`x` equal to `y`; the frontend emits `Hir::mkGlobal("count", …)` and the decomposition
into a sum of indicators is `DecomposeGlobalsPass`'s, per invariant 8. `count` was
previously reported as `E_TYPE: undeclared identifier`, which buckets a coverage gap as
malformed input (§4.3).

This implementation statement does not cover every partial array argument.
Invalid fixed shapes can be evaluation errors, while partial cells and dynamic
selectors have consumer-specific behavior; see the preserved
generator/global observations
and Section 4.2.

**Multi-dimensional parameter arrays are implemented.** `array[1..n,1..m] of int: W`
takes its value from a `[| row | row |]` literal, written either as an initializer or
as a `.dzn`-style assignment, and `W[j,i]` folds to the cell's value. The row-major
order is the *literal syntax's own* — each `|`-delimited group is a row — so unlike the
multi-dimensional *decision* array (§3.4) there is no `EncodingChoice` here: the values
become literals at parse time and no array reaches the output to be flattened. What the
declaration does have to check is that the arrangement it was given is the one declared:
a 3×2 literal and an `array[1..2,1..3]` agree on the cell count and disagree on
everything else, and reading one against the other transposes the data while still
translating. That is refused by name.

**Conditional expressions are implemented** (§4.7). `if c then a else b endif`
reads two ways, chosen by the test. A fixed test selects its branch at parse
time and the others are skipped *without being elaborated*, which is what
MiniZinc's own flattening does and the only reading under which a branch the
test excludes may be undefined. A test on a decision variable keeps both
branches and goes through `Sem::RelationalBuilder::conditional`, so only the
selected branch's definedness is an obligation. `elseif` chains fold one test
at a time; an omitted `else` supplies `true` for a Bool branch and is a type
error otherwise. `div` and `mod`
were the previous entry: the HIR now carries all three
integer-division conventions and the frontend names `Op::DIV_TRUNC` and `Op::MOD_TRUNC`,
because MiniZinc truncates toward zero and takes the remainder's sign from the dividend
(§4.1) — which SMT-LIB's `div`/`mod` do not.

`/` maps to `Op::DIV_REAL`: MiniZinc's `/` is real division whatever its
operands are, and the frontend preserves the language's Int-to-Real coercion.
The coverage item moved only after the result could be stored, passed through
predicates and arrays, optimized, and guarded at zero.

#### Comments, and why they are in the obligations block

MiniZinc has two comment syntaxes: `%` to end of line, and `/* ... */`. They **do not nest**
(specification §3.1), so the first `*/` closes one. The hand-written fixtures used only `%`,
and every file in `instances/upstream/` opens with a `/* */` licence header — which is how a
purely lexical gap made a frontend look like it could not read the language at all.

An **unterminated** `/*` is refused rather than read to end of file, and the reason is the
one this project keeps returning to: the token stream simply ends, so a parser that does not
check sees a *finished* model. A file whose second half was swallowed by a runaway comment
would translate as a smaller model and exit 0. The diagnostic is reported against the
opening `/*`, not against the end of file where it was noticed.

#### `include`: two different things with one syntax

An include of MiniZinc's **standard library** brings in definitions of global constraints;
an include of a **user file** brings in the model. Skipping the first is sound here because
this frontend never uses those definitions — it recognises `alldifferent` and friends by
name and chooses an encoding per profile (§4.3) — so the skip cannot turn an error into a
wrong answer: a global it does not know still fails, at its use site, by name.

Skipping the second could not be sound. `battleships10.mzn` in the corpus is nine lines of
data plus `include "battleships.mzn.model";`, and reading it without the model would
translate the data alone and report success. Eleven of the sixteen upstream files are that
shape, and all eleven are refused. The library list fails **closed**: a name not on it is
refused rather than assumed harmless.

That figure is about the *subset the skeleton targets*, not about MiniZinc — the table
above is the honest picture, and `docs/languages-scoping.md` §3.2 costs finishing the
language at roughly 1.5× the whole skeleton. It read "7 of 8, `set` missing" for several
commits after `set` landed and while `div` was already being refused, which is why the
count now lives in one place and the prose cites it.

### 2.2 The var / par distinction

Every declaration is either **par** (a parameter: fixed at flattening time) or **var** (a
decision variable). `par` is the default when neither is written.

This distinction has no counterpart in the HIR and needs none: a `par` is a constant and is
substituted away, a `var` becomes a `Hir::VarDecl`. The frontend does exactly that — a
parameter's value is evaluated at **parse time** and every occurrence becomes the number,
which is not an optimisation but a requirement: an HIR array does not carry its index set
(§3.1), so `array[1..n] of var int: a` needs n's *value* to know which cells to bound, and
an identifier there would leave those sites with an expression where they need a number.

Three consequences follow, and each is a refusal rather than a guess:

- **An unbound `int: n;` is refused.** In MiniZinc its value arrives from a `.dzn` data
  file, and this frontend reads one file. A model missing it is not a smaller problem but an
  unanswerable one.
- **The value is folded with MiniZinc's own division.** `int: k = (0-7) div 2` is −3, not
  −4: `div` truncates toward zero (§4.1). The fold goes through the ordinary expression
  parser rather than a second evaluator written for constants, so the convention cannot
  drift between a parameter and the same expression in a constraint.
- **Overflow and division by zero are errors.** Wrapping would make `array[1..n]` a
  different array, silently — the same failure profile as an oversized literal.

A parameter and a variable of the same name are refused as a redeclaration. Letting the
later one win would leave every use before it meaning the constant and every use after it
meaning the variable. What it *does* affect is what is legal —
array index expressions, range bounds and `if` conditions in some positions must be `par` —
so a frontend that ignores the distinction accepts models MiniZinc rejects. That is the
lenient direction and costs no fidelity, but it does mean the frontend cannot be used to
validate a model.

### 2.3 The type system

```
bool  int  float  string
set of <T>
array [<index sets>] of <T>
enum
opt <T>                    -- may be "absent", written <>
tuple(...)  record(...)    -- 2.8 series
```

Types are part of the language's cost. The HIR `SortKind` includes `BOOL`, `INT`, and
`REAL`, along with arrays, bit-vectors, floating-point, strings, uninterpreted sorts,
rounding modes, regular languages, datatypes, sets, and tuples
(`include/somtparser/hir/hir.h`). This sort inventory does not mean every MiniZinc
source type or construct is implemented by the adapter; §5 describes the encoding and
refusal boundary for each.

`float` deserves a note because it recurs in `lp.md` and `mps.md`: MiniZinc's
`float` is a real semantically, while solver representations are
implementation-defined. HIR `SortKind::REAL` and `ExprKind::LIT_REAL` preserve
the declarative value exactly; the MiniZinc lexer canonicalizes decimal,
scientific and hexadecimal spellings to rational text rather than passing
through `double`.

### 2.4 Expressions

Arithmetic `+ - * div mod`, comparison `= != < <= > >=`, Boolean `/\ \/ not -> <- <-> xor`,
set operations `in union intersect diff subset`, array access `a[i]`, `if c then a else b
endif`, `let { ... } in e`, comprehensions `[e | i in S where c]`, generator calls
`forall(i in S)(c)`, `sum(i in S)(e)`, whole-array aggregations `sum(x)`, `product(x)`,
`forall(x)`, `exists(x)` — the stdlib's `array[$T]` overloads (handbook 4.2.2.7), folded
over the declared index set, one dimension in source indexing and flattened cells beyond
— and calls to library predicates. Numeric folds accept Bool elements through the
language's automatic Bool-to-Int coercion, lifted elementwise to arrays
([MiniZinc specification](https://docs.minizinc.dev/en/stable/spec.html)).
`forall` over Int and `sum` over String remain type errors. A literal or
comprehension as the direct argument (`sum([1, 2])`,
`sum([e | i in S])`) is read as the handbook's aggregate sugar for the generator form
and emits the same script (landed 2026-09-20).

The expression parser includes Boolean and arithmetic expressions, comparisons,
array indexing, finite aggregates, set expressions, conditional and local bindings,
and the supported global and user-defined predicates described below. Expression
precedence starts at `parseExpr`; individual forms dispatch through `parseAtom`
in `languages/minizinc/src/mzn_minimal.cpp`.

**`->` binds looser than a comparison**, so `constraint b -> x <= 4` is `b -> (x <= 4)` —
the ordinary way to write a half-reified constraint. The lexer produced the `->` token and
nothing consumed it, so that line used to fail with "expected `;`", naming the wrong thing
entirely. A **chain** — `a -> b -> c` — is refused instead of being given an assumed
associativity, because the two readings are different formulas and parenthesising says
which was meant.

`<-` is deliberately **not** a token. Adding it would make `x <-3` lex as `x <- 3`, turning
a comparison against a negative literal into a reverse implication with nothing to signal
it.

### 2.5 Solve and search annotations

```
solve satisfy;
solve minimize x + y;
solve :: int_search(q, first_fail, indomain_min) satisfy;
```

A model has **exactly one** solve item. That rule is now enforced
by the model parser and `parseSolve` in `languages/minizinc/src/mzn_minimal.cpp`;
before 2026-08-11 a model with none
translated to an empty script and exited 0, and a model with two silently became a
two-objective OMT problem. `docs/known-defects-2026-08-11.md` §2.3 records both.

**Search annotations do not change the solution set.** They are strategy hints, so dropping
them is `Fidelity::exact()` for satisfiability and for the optimum. The frontend parses and
skips them wherever they appear — after a declaration, after a constraint, and between
`solve` and its goal — and says so once rather than once per occurrence, since
`q :: add_to_output` appears on every declaration of some models.

That skip is licensed by the specification's own words, which is what separates it from an
`include` of a model file (§2.1): an annotation is *defined* not to change the declarative
semantics, and an included model's constraints are not optional. They *do* change
solving time, which matters for the experiment's fairness argument but is not a fidelity
question — record them in the report rather than in the lattice.

### 2.6 What a solution is

An assignment to every `var` satisfying every constraint; under `minimize`/`maximize`, one
that also optimises the objective. MiniZinc's answer language is `----------` between
solutions and `==========` after the last, with `=====UNSATISFIABLE=====` and
`=====UNBOUNDED=====` among the status lines. The output item decides what is printed,
which matters for differential testing: comparing solver output means comparing whatever
the model's `output` item chose to show, so a translation that drops the output item can
only be compared on verdicts, not on models. Same trap as `dimacs-cnf.md` §3's note about
unused variables and `v` lines.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

### 3.1 What maps exactly

| Construct | HIR representation | New HIR surface | Fidelity |
|---|---|---|---|
| `var bool: b` | `VarDecl{name, Sort::boolean()}` | none | `exact()` |
| `var int: x` | `VarDecl{name, Sort::integer()}` | none | `exact()` |
| `var l..u: x` | `VarDecl{sort = integer(), lower_bound = mkInt(l), upper_bound = mkInt(u)}` | none | `exact()` |
| integer literal | `mkInt(v)` | none | `exact()` |
| `true` / `false` | `mkBool(v)` | none | `exact()` |
| identifier | `mkIdent(name, sort)` | none | `exact()` |
| `/\` `\/` `not` | `Op::AND` / `Op::OR` / `Op::NOT` | none | `exact()` |
| `= != < <= > >=` | `Op::EQ` / `NOT(EQ)` / `Op::LT` … | none | `exact()` |
| `+ - *` | `Op::ADD` / `Op::SUB` / `Op::MUL` | none | `exact()` |
| `constraint e;` | `Constraint{formula = e, soft = false}` | none | `exact()` |
| `solve satisfy;` | `objectives` stays empty | none | `exact()` |
| `solve minimize e;` | `Objective{MINIMIZE, term = e}` | none | `exact()` — subject to §4.4 |
| search annotation | dropped, recorded | none | `exact()` (§2.5) |

This historical table describes operator representations. Its Boolean rows
presuppose correct source-definedness handling (Section 4.2); the `exact()`
label is not a proof of each frontend call site or of model-count preservation.

### 3.2 What has no HIR representation at all

| Construct | Why it does not map | Where §5 puts it |
|---|---|---|
| `array [1..n] of var int` | no array sort, no indexing expression | `SortKind::ARRAY`, `ExprKind::ARRAY_ACCESS` |
| `set of int`, `var set of int` | `SortKind::SET` (landed 2026-08-12) | none |
| `enum` | no enumerated sort | `SortKind::ENUM` |
| `opt int`, `<>` | no absent value | `SortKind::REAL_OPT` and siblings |
| `[e | i in S]` comprehension | no binder | `ExprKind::COMPREHENSION` |
| `forall`/`exists`/`sum` over a generator | the generator is a comprehension | as above |
| `div`, `mod`, `abs` | **no operator**, and see §4.1 | `Op::DIV`, `Op::MOD`, `Op::ABS` |
| `->`, `<->`, `xor` | no operator (expressible via AND/OR/NOT) | `Op::IMPLIES`, `Op::IFF` |
| `if c then a else b endif` | `Op::ITE` (landed 2026-09-20; a fixed test folds, a `var` test uses the relational lazy conditional — §4.7) | none |
| float literal | `ExprKind::LIT_REAL` (landed 2026-08-12) | none |
| `function`/`test` definitions | `FunDecl` with typed binders and an acyclic core-expression body | shared definitions are available; see `docs/hir-defined-functions.md` for scope limits |
| global constraints | `alldifferent` and `count` landed with `DecomposeGlobalsPass`; the rest of the catalogue is still absent | cluster A's shared work |
| `.dzn` data file | `Language::acceptsDataFiles()` returns false by default (`include/somtparser/translation/language.h:105`), so `translate()` refuses a `--data` argument outright rather than parsing the model alone | not a HIR gap |

The `.dzn` row is worth dwelling on because it is a *correct* refusal that looks like a
limitation. `src/translation/translate.cpp:376-388` rejects data files for a language that does not
claim them, and the comment there gives the reason: parsing the model alone and reporting
success for a problem whose data half was dropped is a wrong answer, not a degraded one.
Finishing MiniZinc means overriding `acceptsDataFiles()` and reading the `.dzn` — until
then, refusing is right.

### 3.3 A predicate is a definition, and that decides its representation

`predicate p(var int: a) = a > 0;` looks like it should map onto the HIR's `FunDecl`
(`include/somtparser/hir/hir.h`), which is what cluster G added for TPTP's predicates and
Boogie's functions. It must not. **`FunDecl` is *uninterpreted***: it declares that a symbol
exists and says nothing about what it means. Mapping a MiniZinc predicate onto it throws the
body away, so the predicate may denote anything — and a constraint the model says is
unsatisfiable comes back satisfiable.

That is unsound in the *permissive* direction, which is the hard kind to notice: the emitted
script is well-formed, the solver answers, and the answer is wrong in the direction that looks
like success. It is `hddl.md` §4.1's failure one layer down, and it is worth naming because
the wrong representation is the one the type system would happily accept.

Two representations are correct:

| Route | What it emits | Cost |
|---|---|---|
| **inline** — substitute the body per call site | no symbol at all | duplicates the body; `exact()` |
| **define-fun** — a body-carrying declaration in the HIR | one `define-fun`, calls preserved | new HIR surface; `exact()` |

The frontend inlines in `parsePredicateCall`
(`languages/minizinc/src/mzn_minimal.cpp`), because it is exact, needs no new HIR,
and is what MiniZinc's own flattening does.
Inlining has exactly one hard edge — **a recursive predicate does not terminate** — so
recursion is refused by name rather than attempted, which also keeps it from being reported as
an undeclared identifier and sending a reader after a typo.

The two routes are a genuine second `EncodingChoice`, on the same size-against-structure axis
as ground/quantified, and the frontend records it as one. `Lang::ParseOutcome`
(`include/somtparser/translation/language.h:64`) carries a `TranslationReport` alongside the model and
diagnostics, so an encoding decision made during parsing reaches the same record as one made
by a pass. Recorded once per predicate rather than once per call site, since the decision is
about the predicate; both routes are `exact()`, so what the entry carries is not a loss but
which route ran — and a script with a body duplicated at forty call sites is a very different
object under a solver than one with a single `define-fun`.

### 3.4 Two things the frontend does that are not obvious from the grammar

**Objective names are minted after the whole model is parsed**
by `nameObjectives` (`languages/minizinc/src/mzn_minimal.cpp`). MiniZinc items come in any order, so a
variable called `obj0` declared *below* the solve item still collides with a generated
objective name, and the emitted `(define-objective obj0 OBJECTIVE_MIN obj0)` would rebind a
symbol the script had already declared.

**Expression nesting is bounded at 200 levels**
by `kMaxExprDepth` and `tooDeep` in `languages/minizinc/src/mzn_minimal.cpp`.
This is an implementation limit. Hand-
written MiniZinc does not nest past single digits, and 5000 nested parentheses used to
segfault the process and, through the Python bindings, the interpreter.

---

## 4. Semantic gaps and encoding choices

### 4.1 `div` and `mod` mean different things in MiniZinc and in SMT-LIB

This is the finding of this document.

MiniZinc's `div` is integer division **truncating toward zero**, and `x mod y` takes the
**sign of the dividend** `x`. *(Verified 2026-08-12 against the MiniZinc documentation and
libminizinc issue #97, which states it as "truncated division (towards zero) and its
corresponding remainder operation" and gives `-5 div 3 = -1`, `-5 mod 3 = -2`.)* SMT-LIB's `Ints` theory defines `div` and `mod` by the
**Euclidean** convention, in which the remainder is always non-negative:
`0 ≤ (mod m n) < |n|`.

They agree on non-negative operands and disagree on every negative dividend:

| Expression | MiniZinc | SMT-LIB `Ints` |
|---|--:|--:|
| `7 div 2` | 3 | 3 |
| `(-7) div 2` | **−3** | **−4** |
| `7 mod 2` | 1 | 1 |
| `(-7) mod 2` | **−1** | **1** |
| `(-7) mod (-2)` | **−1** | **1** |

The engine's own operator table maps the symbol `div` straight onto `NT_DIV_INT` and `mod`
onto `NT_MOD` (`include/somtparser/core/kind.h:53`, `:221`), so a frontend that emits the
same spelling gets SMT-LIB's semantics for a MiniZinc source construct.

**Checking that claim found a defect in the engine, not just a trap for frontends.** As
written on 2026-08-12, constant folding matched neither convention *and contradicted
itself*: `NT_DIV_INT` had been corrected to floor semantics — with a comment saying so —
while `NT_MOD`, thirty lines below in the same switch, still used C++ `%`, which truncates.
Each looked defensible alone. Together they broke the identity that defines both:

| | `(div -7 2)` | `(mod -7 2)` | `n·q + r` |
|---|--:|--:|--:|
| what the engine folded to | −4 | −1 | **−9**, not −7 |
| SMT-LIB requires | −4 | 1 | −7 |

Eight of twenty-eight sampled operand pairs violated `m = n·(div m n) + (mod m n)`, and
eight violated `0 ≤ (mod m n) < |n|`. Division by zero additionally threw, rejecting a
script a solver accepts — SMT-LIB's division is *total*, with an unconstrained value, so
there is no constant to fold to and the term must stay symbolic. All three are fixed, and
`test/regression/test_int_div_mod_semantics.cpp` asserts the two laws over a grid rather
than a table of expected values.

**Why this is the most dangerous construct in the document**: nothing catches it. The
translation succeeds, `Fidelity` stays `exact()`, the script round-trips, every test passes,
and the answer is different. It is not even a *lossy* translation — it is a translation of a
different model. Compare §4.2's undefinedness, which at least has the decency to be a known
hard problem.

**The encoding**, once `Op::DIV` and `Op::MOD` exist:

| Option | Form | Fidelity |
|---|---|---|
| Emit `div`/`mod` directly | wrong on negative dividends | **not an option** |
| Correct at the HIR→Parser boundary | truncating division from Euclidean: `t_div(x,y) = ite(x ≥ 0 ∨ x mod y = 0, x div y, x div y + sign(y))`, and `t_mod(x,y) = x − y·t_div(x,y)` | `exact()` |
| Restrict to non-negative operands and assert it | `exact()` where the assertion holds, `E_UNSUPPORTED_CONSTRUCT` where it does not | honest but loses corpus |
| Introduce `Op::DIV_TRUNC` / `Op::MOD_TRUNC` as distinct HIR operators | makes the convention explicit in the IR, so no later frontend can inherit the mistake | `exact()`, **recommended** |

The last option is worth the extra enum entry precisely because this trap is shared: LP and
MPS have no integer division, but Boogie (`boogie.md`) and CryptoLine (`cryptoline.md`) both
do, and each language's convention has to be recorded somewhere. Recording it in the
operator's *name* means a reviewer reading the HIR can see which one was meant.

The engine defect above is the argument for that, made concrete. `NT_DIV_INT` and `NT_MOD`
are named for the *operation*, not the *convention*, so nothing in either name said which
of three possible meanings was intended — and the two drifted apart without any single edit
looking wrong. A `Op::DIV_TRUNC` cannot silently become Euclidean, because the name would
stop matching.

### 4.2 Undefinedness is specified, and it is not what a naive translation gives

For scalar partial arithmetic, definedness closes at the Boolean relation that
consumes the value. It must not be asserted globally. For example, the division
comparison in `b -> 10 div x = 10` becomes
`b -> (x != 0 /\ trunc_div(10, x) = 10)`. The assignment `b=false, x=0`
remains feasible. For an ordinary scalar Boolean array read, `not a[i]`
negates both the selected value and its index guard:
`not (in_range(i) /\ select(a, i))`.

These examples do not define every MiniZinc library operation. Invalid fixed
array data may produce an evaluation error rather than a Boolean value.
Generator-source validity, array shape and partial cells consumed by globals
have separate contracts. The preserved
partial-global controls
and Boolean-index controls
record the observed source/library/runtime combinations and keep failures and
oracle limitations separate from solver answers.

For the four measured `forall`/`exists` forms in
R209,
invalid generator sources remain UNSAT under positive, NOT and double-NOT
constraints. The tested conditional consumes the failed fold as false;
`not (fold default true)` is SAT, whereas `fold default true` and
`(not fold) default true` are UNSAT. These are observed fixture outcomes,
not one general scalar rule. R205 qualification
passed for the promoted implementation, including stronger formula-equivalence
checks for the 20 SAT fixtures.
The 56 cases do not establish propagation through whole-array aliases or
additional Boolean wrappers such as equality and conjunction.

SMT-LIB does the opposite: `div` by zero is **under-specified but total**, so `(div x 0)` is
some fixed unknown value, and `(= (div x 0) 1)` is satisfiable for a solver that chooses to
make it 1. A translation that maps MiniZinc division onto SMT-LIB division therefore turns
an UNSAT model into a SAT one.

| Option | Fidelity | Note |
|---|---|---|
| Map directly and hope no instance divides by zero | unsound in principle, silent | **reject** |
| Carry scalar definedness to its consuming Boolean relation | intended scalar semantic preservation | Scope the guard inside negation/implication as appropriate; this alone proves neither every library contract nor model-count preservation |
| Refuse models containing a partial operation whose definedness is not statically provable | `E_UNSUPPORTED_CONSTRUCT` | defensible under `ParseOptions::strict`; loses corpus |

**Construction introduced on 2026-08-24:** the frontend uses the public
`Uir::Sem::RelationalBuilder`. Arithmetic carries a `PartialExpr{defined,value}`;
the frontend must select the correct value or Boolean consumer for each source
construct. Dynamic division adds `divisor != 0`, and dynamic
array access adds one inclusive bounds predicate per source dimension before
flattening. The translation report records `typed-relational-definedness`, and
`Translation::semantics()` exposes the composed
MiniZinc-to-core and core-to-SMT/OMT contracts.

The builder and contract labels do not establish that every call site chooses
the right scope. R198 caught precisely such a wrong choice under Boolean
negation and conditionals. Independent MiniZinc/Gecode observations and
formula-equivalence checks therefore accompany the repair. Finite observations
establish only the tested cases; they do not prove whole-language conformance.

### 4.3 Global constraints: shared lowering

MiniZinc's `globals.mzn` includes `alldifferent`, `cumulative`, `table`,
`regular`, `circuit`, and many other constraints. Supported frontends share
HIR operators and decomposition passes where the relations coincide; the
XCSP3 catalogue in `xcsp3.md` §4 describes the individual encodings.

For `alldifferent`, explicit terms and finite ground arrays lower to one SMT
`distinct`. Its HIR argument count is linear in the number of elements, with
no finite-domain restriction on the integer values. This replaces the former
quadratic conjunction of pairwise disequalities. The recorded strategy is
`alldifferent-distinct`. Negating it keeps `not(distinct(...))`; n-ary equality
would express a different relation.

The `quantified` profile encodes an indexed array as
`forall i,j. lo <= i < j < hi -> select(a,i) != select(a,j)`. It has constant
structural size and accepts symbolic bounds. Ground encoding requires constant
bounds so it can enumerate the array elements. An explicit term list uses
native `distinct` under either profile because it has no index range to bind.
Both encodings have exact fidelity; independent semantic checks exercise
positive and negative occurrences and nonzero array indices.

`alldifferent_except_0` (also `all_different_except_0`) permits repeated zero
values and requires every nonzero integer to be distinct. It accepts whole
arrays, slices, comprehensions and generator calls. The shared HIR lowering
uses one `distinct` over a linear number of integer expressions: nonzero values
map injectively to positive integers, and each zero receives a different
negative tag. This works for unbounded integers and under negation without
introducing auxiliary variables. Empty and singleton operands retain their
type and definedness checks.

An external `.dzn` file may omit the semicolon after its final assignment,
including before a trailing comment. Internal assignment delimiters remain
required; malformed strings, arrays and comments remain errors.

### 4.4 Optimisation: lowering the objective term

`Hir::Objective` stores one expression, minimized or maximized. MiniZinc's solve
item may supply an expression. The shared `termText` implementation
(in `src/lowering/omt_emitter.cpp`) renders it through the same lowering and
SMT printer used for target terms, rather than restricting objectives to bare
variables or integer literals. Thus a supported expression such as `x + y`
keeps its arithmetic meaning in the emitted objective; unsupported terms must
still produce a diagnostic during validation or lowering. Objective direction
and combination remain part of the translation's semantic contract.

MiniZinc also has no multi-objective solve item, so the engine's `CT_LEX_OPTIMIZE` /
`CT_PARETO_OPTIMIZE` are unused here — `Hir::ObjKind` being poorer than the engine's is not
a limitation for this language.

### 4.5 Unbounded integers and the `bound-ints` pass

MiniZinc allows `var int: x` with no domain. Most CP solvers refuse it or impose a default
range; SMT does not need a bound at all, since `Int` is unbounded.

The project's `bound-ints` pass (`src/lowering/bound_ints_pass.cpp`) exists to impose one
for the *bit-vector* profiles, and it correctly records
`Fidelity::underApprox({BV_WIDTH, w, name})` when it does. For MiniZinc the right default is
the `default` profile, which does not run it: an unbounded MiniZinc integer should stay
unbounded, because SMT can represent it and bounding it would throw away completeness for
nothing.

Note the pass's width is now validated to 1..64 (`src/lowering/bound_ints_pass.cpp:32-38`);
`docs/known-defects-2026-08-11.md` §5.1 records why.

### 4.6 Reification

A constraint used where a Boolean value is expected — `constraint b -> alldifferent(x);`, or
`sum(i in S)(bool2int(c[i])) <= 3` — must be *reified*: the constraint becomes a Boolean
variable constrained to equal its truth value.

An SMT formula is a term of sort Bool, so its Boolean representation needs no
separate reified form. This observation applies after the frontend handles
source definedness and library preconditions; it does not establish those
contracts. FlatZinc's `_reif` predicate variants (`flatzinc.md` §4) make that
representation explicit in the input.

### 4.7 A conditional is two constructs, and the test decides which

`if c then a else b endif` maps to `Op::ITE`, but mapping it that way
*unconditionally* is wrong in both directions, so the frontend reads the test
first.

**When the test is fixed**, MiniZinc's flattening selects a branch and never
elaborates the other one. This is not an optimisation and cannot be replaced by
elaborate-then-discard, for two reasons. First, a branch the test excludes may
have no value: the upstream `tenpenki.mzn.model` is written as

```minizinc
if index_set(x) = {} then … else let { int: n = max(index_set(x)), … } in … endif
```

and `max` of an empty set is undefined — the guard is the *point* of the
conditional. Second, elaboration has effects a model then carries: the `let`
above declares `n` and an array `s` whose size depends on a value the excluded
branch cannot produce. So the untaken branch is skipped at the token level.

**When the test mentions a decision variable**, both branches survive and the
result goes through `Sem::RelationalBuilder::conditional`
([src/translation/semantics.cpp](../../src/translation/semantics.cpp)) rather than `mkOp(Op::ITE, …)`
directly. The difference is the definedness obligation: the adapter emits
`ITE(c, defined(a), defined(b))`, so only the *selected* branch must be defined,
matching §4.2. A bare `Op::ITE` would conjoin both branches' definedness and
refuse `if a != 0 then 100 div a else 0 endif` — a model the specification
accepts and a solver answers.

Condition definedness is a separate question from branch definedness. In the
R209 fixtures above, an invalid `forall`/`exists` generator source used as the
condition selects the false branch. The qualified R205 implementation preserves this measured
behavior; it must not propagate the NOT-specific source guard through the
conditional result. This evidence does not cover arbitrary aliases or wrappers.

`elseif` folds one test at a time rather than elaborating every arm to pick one,
which matters for the same reason: an arm guarded by a test that failed may be
undefined. An omitted `else` supplies `true` when the `then` is Bool, per the
specification, and is a type error otherwise — there is no value to invent for
the missing case, and inventing a zero would answer a different question.

There is no *encoding choice* recorded here. Both readings are exact, and which
one applies is determined by the source rather than chosen by the frontend.

---

### 4.8 Predicates: a body re-parsed per call, array parameters, and `let`

The three tenpenki instances were this frontend's last upstream refusals and
needed one construct each, stacked. They are recorded together because the first
is a change to how *every* predicate is read.

**A predicate body is re-parsed at each call.** It used to be parsed once into
HIR, with the arguments substituted into the finished tree — and `substitute`
said at its own definition why that was only conditionally sound: *"no binders
in a predicate body: no comprehensions, no quantifiers."* tenpenki's body has
both, and worse, its shape depends on the argument: it opens a `let` whose
declarations are **sized** by `max(index_set(x))`. There is no single tree that
every call is an instance of. Re-parsing is the mechanism `forall` already uses
for generator bodies — the ordinary parser under a different binding, with
nesting handled for free — and it removes the no-binders caveat rather than
working around it.

Two things that had to be right:

* **the body carries its whole lexer FRAME, not a position.** A predicate is
  very often declared in an included file — tenpenki puts both of its in a
  `.model` — and every included file is lexed by its own `Lexer` over its own
  source. A bare offset restored while another file's lexer is installed indexes
  the wrong string; the symptom was `E_PARSE: unexpected '' in expression`, at a
  line number belonging to the *caller's* file, for a body that parses.
* **recursion is a SET, not a name.** Parsing the body at the call means `p`
  calling `q` calling `p` reaches the guard, and one "currently defining" name
  could not see it.

**`array [int] of <elem>: x` is a par array parameter**, and the index spec is
`int` because the index set belongs to the *argument*: the body asks for it with
`index_set(x)`. So the argument is read as an array — a literal, or the name of
a par array — and not as an expression, which has a value and no index set. A
literal is indexed **from 1**; `ParamArray::lo` defaults to 0 and is re-based by
a declaration, which a literal argument never has, so leaving it gave `[1, 3]`
the index set `0..1`, `max(index_set(x))` came back 1 instead of 2, and the
model still translated.

**`let { int: n = …, array [lo..hi] of var D: s } in e`** declares from
expression position, where the model is not in scope, so the declarations are
queued and drained by the item that owns the expression. The property that
matters is **one array per call**: `let` is opened once per call, tenpenki calls
`row_constraint` five times, and each row needs its own starting-column array.
Sharing one between two rows constrains the rows to have identical blocks — a
wrong answer, not a refusal, and invisible to any check that asks only whether
the file translated. The declaration therefore takes a fresh name (`s@let0`,
`s@let1`, …; `@` is not a MiniZinc identifier character, so a generated name
cannot collide with one a model wrote) and the body reads through an alias.

**How it was verified.** tenpenki_1 publishes its own solution in its header, so
the translation was checked against it rather than against "it translated":
asserting the published grid is **sat**, asserting it with one cell flipped is
**unsat**, and the model with no grid asserted is **sat**. The first rules out an
over-constrained translation, the second an under-constrained one. The first
attempt at that check appended its assertions *after* the emitted script's own
`(check-sat)`, so both answers were `sat` and meant nothing — worth recording,
because a solver that answers the wrong question looks exactly like a solver
that answers this one.

## 5. New HIR surface this format forces

MiniZinc forces more new HIR than any other language in the batch except TPTP, which is why
`docs/languages-scoping.md` §3.2 costs finishing it at ~1.5× the whole skeleton. Grouped by
whether the language can be usefully translated without it:

**Blocking — a large fraction of the corpus is unreachable without these**

| Surface | Why | Shared with |
|---|---|---|
| `SortKind::ARRAY` + `ExprKind::ARRAY_ACCESS` | almost every non-toy model declares an array | FlatZinc, XCSP3, Essence′ |
| `ExprKind::COMPREHENSION` (a binder over an index set) | `forall`, `exists`, `sum` are all generator calls | XCSP3, Essence′ |
| a global-constraint call form | `globals.mzn` is the language's point | the whole of cluster A |
| `Op::DIV`, `Op::MOD` — **with the convention in the name**, per §4.1 | arithmetic models | Boogie, CryptoLine |

**Non-blocking — expressible today, but clumsily**

| Surface | Today's workaround | Cost of not having it |
|---|---|---|
| `Op::IMPLIES`, `Op::IFF` | `OR(NOT a, b)` and a conjunction of two implications | doubles the node count of implication-heavy models; `mkOp` is n-ary so this is mechanical |
| `Op::ITE` | expand into a conjunction of guarded cases | exponential on nested conditionals |
| `Op::ABS` | `ITE(x ≥ 0, x, −x)`, i.e. needs `ITE` first | — |
| ~~`ExprKind::LIT_REAL`~~ **landed 2026-08-12** | `var float` constants are writable | was blocking float models entirely; shared with `lp.md`, `mps.md` |

**Deferred — real MiniZinc features with no cheap encoding**

`SortKind::ENUM` and option types — `SortKind::SET` landed on 2026-08-12. Sets over small
universes encode as bit-vectors or Boolean arrays; over large or unbounded ones they do not.
Enums are a labelling on top of `Int` and are mostly a diagnostic-quality question. Option
types change the *shape* of satisfaction and deserve their own decision rather than an
encoding.

---

## 6. Fidelity summary

**Exact — the skeleton's whole surface.** Every construct in §3.1: Boolean and integer
variables, integer range domains, the six comparisons, `+ - *`, `/\ \/ not`, constraints,
and a single-variable objective. Search annotations are dropped, which is exact for both
satisfiability and the optimum (§2.5).

**Exact, once the surface exists.** Arrays with fixed index sets, comprehensions over fixed
generators, implication and equivalence, conditionals, reification (§4.6), and most global
constraint decompositions (§4.3).

**Inherently lossy: very little.** MiniZinc's semantics is a good fit for SMT. The genuinely
lossy cases are:

- Global constraints whose only practical encoding bounds a domain — `underApprox` with
  `Bound::DOMAIN_CUT`.
- Float models if a backend deliberately lowers mathematical Real to a fixed
  floating-point format. The MiniZinc-to-SMT path here does not do that; it
  targets SMT Real exactly.
- Set variables over large universes, if encoded by bounding the universe.

**Ways to make it lossy by mistake** — all avoidable, all listed so a reviewer can check
they were avoided:

- Emitting `div`/`mod` with SMT-LIB's Euclidean semantics for MiniZinc's truncating ones
  (§4.1). **Silent. No fidelity value describes it, because it is not a loss — it is a
  different model.**
- Mapping partial functions onto SMT's total-but-underspecified ones, turning UNSAT into
  SAT (§4.2).
- Parsing the model and ignoring its `.dzn` — refused by construction today (§3.2), and the
  refusal must survive `acceptsDataFiles()` being switched on.
- Dropping the output item and then comparing models rather than verdicts (§2.6).
- Accepting two solve items, or none — fixed, and covered by
  `test/languages/test_mzn_input_validation.cpp`.

**Not applicable**: `preserves_optimum` for `solve satisfy` models, in the same "vacuously
true" reading `dimacs-cnf.md` §2.2 uses.

---

## 7. References

**Language specification**

1. The MiniZinc Handbook, including the language specification chapter.
   <https://docs.minizinc.dev/> — **exact version not re-confirmed in this pass**; pin it
   before implementation, per `docs/languages-scoping.md` §1.2.
2. SMT-LIB `Ints` theory declaration, for the Euclidean `div`/`mod` semantics §4.1 compares
   against. <https://smtlib.cs.uiowa.edu/theories-Ints.shtml>

**Competition and corpus**

3. MiniZinc Challenge. <https://www.minizinc.org/challenge/> — per-year instance archives,
   solver ranking and rules. Instance counts and licence terms **not re-confirmed**.
4. `libminizinc`, the reference implementation and flattener. Repository, licence and
   release **not re-confirmed**; also the natural oracle for §4.2.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster A), §3.2 (1.0× baseline, +1.5× to finish),
   §4 (Plan 2), §6 (the second filter), §7 (competition audit).
6. `docs/superpowers/specs/2026-08-10-languages-design.md` §4.1 (the `Fidelity` lattice),
   §4.7 (HIR), §6.1 (language-directory boundary rules), §10 (testing strategy).
7. `docs/known-defects-2026-08-11.md` §2.3 (the solve-item rule), §2.5 (objective-name
   collisions), §5.1 (the `bound-ints` width range).
8. `docs/languages/dimacs-cnf.md` §2.2 (the vacuous-`preserves_optimum` reading), §3
   (models-versus-verdicts in differential testing).
9. `docs/languages/flatzinc.md` §1 (the flattening boundary, stated from the other side),
   §4 (reification as FlatZinc sees it).
10. `docs/languages/lp.md` §4 and `docs/languages/mps.md` §4 (the missing real literal).
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `include/somtparser/translation/language.h`, `src/translation/translate.cpp`,
    `src/lowering/omt_emitter.cpp`, `src/lowering/bound_ints_pass.cpp`,
    `languages/minizinc/src/mzn_minimal.cpp`, `include/somtparser/core/kind.h`.
