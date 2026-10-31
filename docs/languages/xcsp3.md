# XCSP3 — an XML format for CSP and COP

**Date**: 2026-08-25
**Status**: **implemented for XCSP3-core integer variables, objectives, all 22 core
constraint names, lifted list/matrix forms, and `group`/`block`/`slide`**
(`languages/xcsp3/`, `test/languages/test_xcsp3.cpp`). Exact auxiliary encodings cover
`regular`, `mdd`, and sub-`circuit`; model projection omits those witnesses. `div` and `mod`
use truncation toward zero with an explicit nonzero-divisor definition guard (§4.1).
Sum/count lists, scalar allDifferent lists and specialized objective lists accept integer functional expressions,
including predicates interpreted as 0/1; partial expressions retain their
definedness guards. Numeric/variable mixtures are accepted in term lists.
Set conditions accept `{0,2,4}` as well as `set(0,2,4)`. Instantiation values
and objective coefficients accept integer repetitions such as `1x8`; their
expanded lengths must match the accompanying list.
Array `as` declarations copy the earlier declaration's content while retaining
their own shape and start index. The reference must precede the alias, must not
itself be an alias, and must not contain nested IDs; the alias cannot contain
its own domain text. This follows [XCSP3 §10.5](https://arxiv.org/pdf/1611.03398).
Mixed-domain arrays may leave cells undefined; those cells introduce no HIR
variable, and using one in a constraint or objective is an error. An explicit
empty domain instead produces an unsatisfiable model, as required by §2.10.
Scalar allDifferent expression views, including `except`, preserve definedness
of every operand and the selected branch of conditional expressions (§10.4).
Singleton sums and counts emitted by competition generators retain their
ordinary one-term/one-indicator semantics; empty lists are rejected.
The full-format `flow` constraint additionally supports integer arc variables,
node balances, optional signed capacity intervals, and an optional weighted-cost
condition. Node labels form a consecutive integer range; balances follow that
range from its minimum label. Each equation is outgoing flow minus incoming
flow, including parallel arcs and self loops. Balances and weights may be
integer literals or declared integer variables. No nonnegative-flow assumption
is added. Conservation, capacities, and cost compose through the shared typed
integer HIR without extra witness variables. Sparse node labels and semantic
attributes such as reification are explicitly rejected. The contract follows
[XCSP3 3.2, Syntax 74 and Semantics 45](https://arxiv.org/pdf/1611.03398v5#page=94)
and the [official checker's node-index convention](https://github.com/xcsp3team/XCSP3-Java-Tools/blob/7d7b92460e5f3add9a965b5a4668bb2d8aad6d6d/src/main/java/org/xcsp/parser/callbacks/SolutionChecker.java#L1072).
Generalized `intExpr` views in every global-list position and full-XCSP3 non-integer
variable families remain outside the declared surface. The local XML reader intentionally
supports no namespaces or DTD and recognizes only the five predefined entities.
**Scoping context**: `docs/languages-scoping.md` §3.1 cluster A, §3.2 (cost **2.0×**), §4.

<!-- proposed-hir: SortKind::ENUM, ExprKind::ARRAY_ACCESS, ExprKind::COMPREHENSION, Op::IFF -->
<!-- Proposed HIR, not existing HIR. See scripts/check-doc-citations.py. -->

**Headline result of the audit in §4**: extension tables and automaton/global expansions
dominate output size, while the correctness risks come from semantic details: sparse domains,
short/conflict tables, partial division, subcircuit connectivity, tuple lifting, and objective
order. These are represented explicitly rather than inferred from XML shape.

The **objectives** were a second finding and are now **implemented**. XCSP3 has seven
objective *expressions* (`sum`, `product`, `minimum`, `maximum`, `nValues`, `lex`, plus a
plain variable or expression) and, in the **full** format, a multi-objective form combining
several by `lexico` or `pareto`. Two corrections have been applied since the first draft:

- **XCSP3-core permits only one objective.** The specification says "for XCSP3-core, only
  one element can be present in `<objectives.../>`", and its skeleton writes the content as
  the alternation `( <minimize/> | <maximize/> )` rather than a repetition. So the
  multi-objective form is a *full*-XCSP3 concern, not a core one — and an earlier draft made
  it the headline while also recommending core, which cannot both be true. Verified against
  arXiv:2009.00514 on 2026-08-12.
- **The HIR now carries it anyway.** `Hir::ObjectiveCombination`
  (`include/somtparser/hir/hir.h`) has `LEXICOGRAPHIC`, `PARETO`, `BOX`, `MINMAX` and
  `MAXMIN`, mirroring the engine's own `OPT_KIND`, and `omt_emitter` renders the first three
  for Z3 as `(set-option :opt.priority lex|pareto|box)`. That is not for XCSP3's sake: OMT
  is this project's headline capability, this engine already *reads* five multi-objective
  commands, and until the field existed a multi-objective model emitted several
  `(minimize t)` commands whose documented Z3 default is lexicographic — so the pipeline was
  not losing the combination, it was silently choosing one.

<!-- implicit-constraints:
  an explicitly empty integer domain => false, because the source variable admits no value (§2.10)
  an unselected mixed-domain array cell => no source declaration; using it in a constraint or objective is rejected (§2.10)
  a sparse domain `1 3 5 7` => a membership constraint, because VarDecl carries only two bounds; reading it as the range 1..7 admits solutions the instance forbids (§2.2, §4.4)
  circuit => position variables or subtour elimination; pairwise distinctness alone admits sub-cycles and is unsound (§4.3)
  a conflicts table => forbids exactly the listed tuples; its complement is the supports table only over the full Cartesian product of the declared domains (§4.2)
  a short table's `*` wildcard => matches every value in that column's declared domain; treating it as a literal is wrong, while omitting its local guard is exact only when the declaration domain is globally enforced (§4.2)
  multiple objectives with combination lexico or pareto => preserve the combination explicitly; an unordered list answers a different question (§4.5)
  div(x,y) and mod(x,y) => Java / and % semantics (truncate toward zero, remainder follows dividend), with y != 0 closed at the containing Boolean constraint (§4.1)
-->
---

## 1. What the format is

XCSP3 is an XML format for representing constraint satisfaction (CSP) and constraint
optimisation (COP) instances, designed as a *lingua franca* for the CP community and used
by the XCSP3 competition series. Its distinguishing feature against MiniZinc is that it is
an **instance** format, not a modelling language: there is no user-defined predicate, no
comprehension over a computed set, no parameter file. Everything is ground, which is why
`docs/languages-scoping.md` §3.2 costs it at 2.0× on *catalogue breadth* rather than on
grammar depth.

### XCSP3 and XCSP3-core

The specification defines a large format and a **core subset**. XCSP3-core is what
competition instances use and what solvers are expected to support: integer variables,
around twenty constraint families, and the objective forms of §2.4. The full format adds
symbolic, set, real and graph variables, and a longer constraint list.

**Target XCSP3-core.** The full format's extra variable types each need HIR that nothing
else in the batch needs, and the corpus does not use them. Say so explicitly in the
frontend's `OpCoverage` rather than silently accepting a subset.

### Standard documents

| Document | Version / date | URL |
|---|---|---|
| *XCSP3: An Integrated Format for Benchmarking Combinatorial Constrained Problems*, Boussemart, Lecoutre, Audemard, Piette | the format specification; **exact current revision not re-confirmed in this pass** | <http://xcsp.org/> |
| XCSP3-core specification | the competition subset | <http://xcsp.org/> |
| XCSP3 competition series | per-edition rules, solvers and results | <http://xcsp.org/competitions/> |

**Version and licence terms not re-confirmed in this pass**, the same open item
`docs/languages-scoping.md` §1.2 and §1.7 record for QBFLIB and TPTP.

### Reference implementation and corpus

The XCSP3 project publishes parsers (Java and C++) and the competition publishes instance
archives per edition. ACE and Choco are the reference-quality solvers. **Repository URLs,
licences and versions not re-confirmed**; pin them before differential testing.

A practical note that affects the frontend's shape: XCSP3 instances are XML and are
distributed compressed, often reaching tens of megabytes uncompressed because of extension
constraints (§4.2). Both the XML tree and expanded constraint formulas can dominate
memory use. Compact group templates can produce many more formula nodes than the
source size suggests; dense-table complementation below addresses one such case.

The file entry point reads XML through a 64 KiB window. It retains parsed XML
nodes, with one shared immutable buffer per distinct decoded table text, rather
than keeping the complete source file alongside the tree. Table storage can be
shared across scopes and polarities; domain checks and `supports`/`conflicts`
semantics remain local to each constraint. Template substitution materializes a
private copy when table text contains formals. The inline entry point continues
to borrow entity-free table views from the caller's source. Neither entry point
streams the entire HIR: the tree and resulting formulas still consume memory.
Certified finite product domains are compacted when each XML leaf closes, so
their original enumeration is not retained in the tree (§2.2).

---

## 2. Semantics — what a file means

### 2.1 Structure

```xml
<instance format="XCSP3" type="COP">
  <variables>
    <var id="x"> 0..10 </var>
    <array id="q" size="[8]"> 1..8 </array>
  </variables>
  <constraints>
    <allDifferent> q[] </allDifferent>
    <intension> le(add(x, 3), 10) </intension>
    <group>
      <intension> ne(%0, %1) </intension>
      <args> q[0] q[1] </args>
      <args> q[0] q[2] </args>
    </group>
  </constraints>
  <objectives>
    <minimize type="sum"> x q[0] </minimize>
  </objectives>
</instance>
```

`type` is `CSP` (no objectives) or `COP`. The three sections are ordered and each is
optional except `<variables>`.

### 2.2 Variables and domains

XCSP3-core has **integer** variables. A domain is a set of values and ranges:
`0..10`, `1 3 5 7`, `0..3 7 9..12`. Arrays are declared with a size vector and may give
different domains to different slices.

Two things a frontend must not skip:

- **A domain is not just a pair of bounds.** `1 3 5 7` is not `1..7`. Translating it as a
  range would *weaken* the model — more solutions than the original, `complete = true` but
  `sound = false`. It must become a disjunction, or a range plus exclusions, or an
  `int_in`-style membership. The HIR's `VarDecl` has exactly `lower_bound` and
  `upper_bound` (`include/somtparser/hir/hir.h`), so a non-contiguous domain has to
  be expressed as an ordinary constraint, not as a declaration.
- **Array slices** (`q[]`, `q[0..3]`, `q[][0]`) are notation over a declared array, not new
  variables.

An explicit sparse list forming an arithmetic progression uses its original
bounds and `(mod (- x lo) step) = 0`. The frontend checks every adjacent gap
before choosing this encoding and keeps the original enumerated domain for
other constraints. A non-progression list whose complement inside its bounds
has no more values than the list uses `distinct(x, missing_1, ..., missing_k)`.
The missing constants are distinct, so this excludes exactly those values;
for `-1 1`, the membership is simply `distinct(x, 0)`. Other lists retain
explicit membership. Independent
relation checks include negative bounds and signed-endpoint distances.

A strictly increasing explicit list can also be certified as exactly
`{a*b | -n <= a,b <= n}`. The reader generates the product set independently,
checks every listed value and its cardinality, then stores only `n`. Membership
lowers to `exists a,b. -n <= a,b <= n and x = a*b`, with local bound variables;
the original minimum and maximum remain declaration bounds. This preserves
holes, including primes between `n` and `n*n`. Recognition is limited to
decoded texts of at least 1024 bytes and `n <= 2048`; lists outside that
optimization budget or failing any check use the ordinary domain parser.
No filename, variable name, or benchmark identifier selects this encoding.
Table sharing compares the certified domain too; table complementation keeps
its original encoding for such domains. This introduces bounded nonlinear
existential constraints and may change solver performance even though the
relation is exact. Exhaustive small-domain solver checks cover membership,
changed lists, array aliases, table polarity, and binder-name collisions.

Repeated intension subexpressions at the same source location share immutable
nodes together with their definedness. For division/remainder, a known nonzero
integer denominator needs no additional guard; a zero or symbolic denominator
retains its definedness condition. Lazy conditionals still require only their
selected branch to be defined.

### 2.3 Constraints

XCSP3 predicates have numeric values 0 and 1. Numeric argument positions,
including reified equalities such as `eq(a,gt(x,y))`, therefore lower a predicate
to `ite(predicate,1,0)` before applying the integer operation. This conversion
uses the relational builder: undefined operands remain undefined, and an
unselected conditional branch does not impose its definedness obligation.
HIR itself continues to distinguish `Bool` from `Int`. See the
[official intension semantics](https://xcsp.org/specifications/constraints/generic/intension/).

The September 2026 audit in `tools/audit_xcsp3_boolean_values.py` checks 23
independent Python truth tables against emitted SMT, including partial division
and conditional branches, and replays the 13 affected IndusCP models. Successful
translation of these models is distinct from independent target parsing and
full source-model equivalence.

Compact integer repetitions (`1x3`) also work in scheduling lengths and other
mixed term lists. Lexicographic comparisons accept nonempty equal-length lists,
including singleton lists. For `nValues` without exclusions, conditions asking
whether the list has one or multiple distinct values use comparisons with the
first entry instead of first constructing the full distinct-value count.

Scalar `allDifferent` without exceptions lowers through the shared HIR pass to
one native SMT `distinct` with one argument per term. Indexed ground arrays
select each element once; quantified array profiles retain their guarded
quantifier encoding. Exceptions and tuple comparisons retain their own exact
encodings. Negating a native `distinct` preserves the negation: it means that
some pair is equal, not that every term is equal.

Extension tables are parsed into a contiguous signed-integer array plus a
wildcard bit vector. Integer cells are validated once before complementing or
factoring the relation. No integer value is reserved for `*`, including either
signed 64-bit endpoint.

XCSP3-core's catalogue, grouped by what a translation does with each. This is the table
`minizinc.md` §4.3 and `flatzinc.md` §4.4 both defer to.

| Family | Form | To SMT | Fidelity |
|---|---|---|---|
| `intension` | a predicate expression tree | direct, operator by operator | `exact()` |
| **`extension`** | explicit tuple table, `supports` or `conflicts` | **§4.2** | `exact()`, at a size cost |
| `regular` | a DFA over a variable sequence | unroll the automaton: one state variable per position | `exact()` |
| `mdd` | a multi-valued decision diagram | as `regular`, over the DAG | `exact()` |
| `allDifferent` | optionally with `except` values, or on lists/matrices | pairwise `≠`, or `distinct` | `exact()` |
| `allEqual` | | chain of `=` | `exact()` |
| `ordered`, `lex` | `≤`/`<` along a sequence, lexicographic on lists | direct; `lex` needs the standard chain encoding | `exact()` |
| `sum` | `Σ cᵢ·xᵢ ⋈ k`, possibly with variable coefficients | direct (variable coefficients make it non-linear) | `exact()` |
| `count`, `atLeast`, `atMost`, `exactly` | how many `xᵢ` take a value | `Σ ITE(xᵢ = v, 1, 0) ⋈ k` | `exact()` |
| `nValues` | number of distinct values taken | harder: needs a value-occurrence encoding | `exact()`, larger |
| `cardinality` | per-value occurrence bounds | a `count` per value | `exact()` |
| `minimum`, `maximum` | `y = min(x…)` | `⋀ y ≤ xᵢ ∧ ⋁ y = xᵢ` | `exact()` |
| `element` | `x[i] = v` with variable index | as `flatzinc.md` §4.3 | `exact()` |
| `channel` | two arrays are inverse permutations | pairwise biconditionals | `exact()` |
| `noOverlap` | rectangles/tasks do not overlap | disjunction per pair | `exact()` |
| `cumulative` | resource profile over tasks | finite start/end events and zero-load baseline | `exact()` (§4.3) |
| `circuit` | non-self successors form one nontrivial cycle | needs subtour elimination or position variables | **§4.3** |
| `instantiation` | fix variables to values | equalities | `exact()` |
| `slide` | a constraint applied along a sliding window | expand | `exact()` |

### 2.4 Objectives

```xml
<objectives combination="lexico">        <!-- full XCSP3 only; core allows one -->
  <minimize type="sum"> x1 x2 x3 </minimize>
  <maximize type="minimum"> y1 y2 </maximize>
</objectives>
```

- A **single** objective is `<minimize>` or `<maximize>`, either over an expression or with
  `type` ∈ {`expression`, `sum`, `product`, `minimum`, `maximum`, `nValues`, `lex`}, over a
  list with optional coefficients.
- **Multiple** objectives are combined by `lexico` or `pareto`.

§4.5 is about this.

### 2.5 Groups, blocks and the `%i` notation

`<group>` factors a constraint template over many argument tuples; `<block>` groups
constraints for readability and tagging; `%0`, `%1` are the template's parameters.
Compact array slices in `<args>` expand in index order before `%i` and `%...`
are substituted, as specified in the [official group syntax](https://xcsp.org/specifications/constraints/groups/).
For example, `x[0..2]` supplies three arguments, and `x[0] x[2..3]` also supplies
three. Whitespace inside a functional argument does not split that argument.

**These are syntax, not semantics.** Expanding a group yields exactly the constraints it
abbreviates. There is no fidelity question and no encoding choice — but there is a size
question: a group of 10⁵ tuples expands to 10⁵ HIR constraints, and `dimacs-cnf.md` §4.4's
memory arithmetic applies directly.

---

## 3. Construct → HIR mapping

Target: `SOMTParser::Uir::Hir` as it exists at `include/somtparser/hir/hir.h` today.

| Construct | HIR representation | New surface | Fidelity |
|---|---|---|---|
| `<var> l..u` | `VarDecl{integer(), lower_bound, upper_bound}` | none | `exact()` |
| `<var>` with a non-contiguous domain | `VarDecl` bounds + a membership `Constraint` | none | `exact()` (§2.2) |
| `<array>` | one `VarDecl` per element, or an array sort | `SortKind::ARRAY` | `exact()` either way |
| `intension` arithmetic `add/sub/mul` | `Op::ADD` / `SUB` / `MUL` | none | `exact()` |
| `intension` `div`/`mod` | **§4.1** | `Op::DIV_TRUNC`, `Op::MOD_TRUNC` plus `y != 0` | `exact()` |
| `intension` `abs`, `min`, `max`, `dist` | via `ITE` | `Op::ABS`, `Op::ITE` | `exact()` |
| `intension` `lt/le/gt/ge/eq/ne` | `Op::LT` / … / `NOT(EQ)` | none | `exact()` |
| `intension` `and/or/not/xor/imp/iff` | `Op::AND` / `OR` / `NOT`; the last three via combinations | `Op::IMPLIES`, `Op::IFF` for directness | `exact()` |
| `intension` `if` | — | `Op::ITE` | `exact()` |
| `extension` | §4.2 | needs arrays for the tuple lists | `exact()` |
| global constraints | §2.3's table; cluster A's shared pass library | as each row | mostly `exact()` |
| `<group>` / `<block>` | expanded (§2.5) | none | `exact()` |
| single objective over a variable | `Objective{kind, mkIdent(x)}` (`include/somtparser/hir/hir.h`; identifier construction: `include/somtparser/hir/hir.h`) | none | `exact()` |
| objective `type="sum"` etc. | needs the aggregate as a term | none for `sum`; `Op::ITE` for `nValues` | `exact()` |
| **multi-objective** `lexico` / `pareto` — full XCSP3 only, not core | `ConstraintModel::objective_combination` | **none — implemented** | `exact()` |

---

## 4. Semantic gaps and encoding choices

### 4.1 `div` and `mod`, again — and XCSP3 states its convention

XCSP3's `intension` language has `div` and `mod`, written as `/` and `%` in the official
operator table and implemented by the official Java tooling with Java integer semantics:
division truncates toward zero and the remainder follows the dividend. The frontend maps
them to `DIV_TRUNC`/`MOD_TRUNC`, not SMT-LIB's Euclidean `div`/`mod`, and records `y != 0`
as expression definedness so it closes at the containing Boolean constraint.

`minizinc.md` §4.1 has the full table, the failure mode, and the recommendation to put the
convention in the HIR operator's name. This document does not restate it. What it adds is
that XCSP3 is the **third** language in the batch to hit it, after MiniZinc and FlatZinc,
with Boogie and CryptoLine still to come — which is the argument for `Op::DIV_TRUNC` and
friends rather than a per-frontend correction repeated five times.

`test/languages/test_division_conventions.cpp` covers a negative dividend and a dynamic
zero divisor, so using bare SMT-LIB division or a global nonzero guard fails mechanically.

### 4.2 Extension constraints are the language's real cost

An `extension` constraint lists the allowed (`supports`) or forbidden (`conflicts`) tuples
explicitly:

```xml
<extension>
  <list> x y z </list>
  <supports> (0,0,0)(0,1,1)(1,0,1)(1,1,0) </supports>
</extension>
```

Real instances have tables with 10⁴–10⁶ tuples. This is where XCSP3 files get large and
where the encoding choice is a research question rather than a lookup.

| Encoding | Form | Size | Fidelity | Note |
|---|---|---|---|---|
| Direct disjunction (supports) | `⋁ₜ ⋀ⱼ (xⱼ = tⱼ)` | O(rows × arity) | `exact()` | the obvious one; large but simple |
| Direct conjunction (conflicts) | `⋀ₜ ⋁ⱼ (xⱼ ≠ tⱼ)` | O(rows × arity) | `exact()` | the dual; note the *complement* of a conflicts table is not the supports table unless the domains are known and finite |
| MDD / DFA compression | compile the table to an MDD, then encode as `mdd` | O(MDD size) | `exact()` | often a large win; the compilation is the work |
| Tseitin-style with selector variables | one Boolean per row, exactly-one over rows | O(rows) clauses + rows variables | `equisat()` — auxiliary variables preserve satisfiability both ways | changes the model's vocabulary, so the `Fidelity` is `equisat`, not `exact` |

The `equisat` row distinguishes satisfiability from counting.
`CountStatus::NO_GUARANTEE` and `CountStatus::UNASSESSED` are declared in `include/somtparser/translation/fidelity.h:25-28`.
`Fidelity::equisat()` sets `NO_GUARANTEE` in `src/translation/fidelity.cpp:78-93`.
`Fidelity::exact()` returns a default-constructed fidelity (`src/translation/fidelity.cpp:74-75`).
The `count_status` field defaults to `CountStatus::UNASSESSED` (`include/somtparser/translation/fidelity.h:75`).
Neither status asserts a measured count mismatch. A one-sided auxiliary can multiply the model count
while preserving satisfiability in both directions; a functionally determined
auxiliary can preserve it. A `PRESERVED` claim needs an explicit count obligation
and recorded evidence at the encoding site; the validator checks this metadata,
not a counting proof. The report does not infer that claim from the number of
auxiliaries or from feasibility preservation.

**A supports/conflicts trap**: a `conflicts` table forbids the listed tuples *and nothing
else*, so its negation is only equivalent to a supports table over the full Cartesian
product of the declared domains. Translating one into the other without that product is a
soundness error, and it is easy to do while "simplifying".

**Short tables** (`*` as a wildcard in a tuple) compress rows and must preserve the
meaning "any value in this column's declared domain"; treating `*` as a literal is
a silent wrong answer. The complete model enforces each declared domain, so its
wildcard factor can be omitted locally.

Dense ordinary tables use the smaller complement when it can be enumerated over
the complete declared Cartesian product within 250,000 cells. The frontend
retains exact sparse-domain constraints, removes duplicate and out-of-domain rows
from the membership set, and swaps supports/conflicts polarity only after
constructing that complement. Wildcard tables stay on the direct/factored path;
their wildcard cells add no local factor because every variable's complete
declared domain is already enforced by bounds or sparse-domain constraints.
This adds no variables and preserves the full source relation. For example, the
five-colour Ramsey table lists 120 allowed triples out of 125; the equivalent
encoding forbids only the five monochromatic triples. The table semantics are
specified in the [XCSP3 specification](https://www.cril.univ-artois.fr/~lecoutre/papers/CJ20_xcsp3.pdf).

Shared suffix relations are factored before allocating equality expressions.
A complete label set may become one exact arithmetic progression, or a union of
maximal contiguous intervals and singleton values, when this reduces expression
construction cost. Holes remain excluded; sparse declaration domains remain
globally enforced. A label set covering every declared value contributes no local
guard. These rewrites add no witnesses or quantifiers.

File input is read into one owned buffer in bounded chunks. A regular file's size
is only a reservation hint; sources without a usable size are still read to EOF.
Borrowed table views remain valid until their constraints have been lowered.

### 4.3 Scheduling, automata, and subcircuits

The implemented `cumulative` encoding enforces the load condition at every integer time,
including negative origins and the zero load outside task intervals. For a task with origin
`s`, length `d`, and height `h`, its contribution is `h` exactly when `s <= t < s+d`.
The load changes only at task starts and ends, so the frontend checks the original
condition at every start/end event and separately at load zero. This is equivalent to
the previous universal integer-time relation without enumerating a scheduling horizon.
Checking both event kinds also covers signed heights and arbitrary supported conditions,
including equality and set membership. Larger relations share an exact load definition;
this introduces no unconstrained relation. Optional end variables remain tied to
`origin + length` explicitly, and objectives are unchanged.

This time-domain policy is explicit because reference descriptions differ: the
[XCSP3 Core 3.2 document](https://arxiv.org/pdf/2009.00514) writes natural time in
Semantics 25, whereas the pinned
[official Java SolutionChecker](https://github.com/xcsp3team/XCSP3-Java-Tools/blob/83194b0de766fe7252a56c7ced650dbc56d07eb7/src/main/java/org/xcsp/parser/callbacks/SolutionChecker.java#L1126)
checks from the minimum origin through the maximum end, including negative origins
and the final zero-load point. The frontend preserves its existing all-integer-time
semantics. With nonnegative lengths, this agrees with that Java range check. It does
not claim checker agreement for arbitrary negative lengths: if every end precedes
every origin, the Java range can be empty, while the frontend still requires the
zero-load condition. Such cases remain explicit compatibility boundaries rather than
being silently changed or counted as official-conformance results.

For `binPacking`, an array of `<limits>` or `<loads>` constrains every listed bin, including
empty bins with load zero. A single uniform `<condition>` applies to the bins used by items.
These two forms therefore differ when a condition excludes zero.

`regular` and `mdd` use one Boolean reachability witness per layer/state. The transition
equivalences and final-state disjunction are exact for finite words; the generated witnesses
are target-only symbols and are removed by model projection.

XCSP3 `circuit` is a **subcircuit**, not necessarily a Hamiltonian cycle: unused nodes map to
themselves, while all non-self arcs form one cycle of size greater than one. Successor bounds
and `allDifferent` establish a permutation; active-node position witnesses enforce one
connected nontrivial cycle and the optional `<size>` equals the active-node count. Pairwise
distinct successors alone would admit several disjoint cycles and is unsound.
Active positions use one SMT `distinct`, with disjoint negative tags for
inactive entries. Successor positions are selected from one fully defined
array, avoiding a constraint for every possible arc. Its outside-domain
default is fixed and unobservable under the successor bounds, so this sharing
adds no unconstrained array witness.

### 4.4 Non-contiguous domains

Covered in §2.2 as a semantic point; repeated here as an encoding one because it is the
most likely first bug. `VarDecl`'s two bounds cannot express `1 3 5 7`. The options are a
membership disjunction (`⋁ x = vᵢ`, O(|D|)), a range plus exclusions
(`l ≤ x ≤ u ∧ ⋀ x ≠ gapᵢ`, O(gaps)), or — where the domain is dense — the bounds alone,
which is **wrong** unless the gaps are genuinely empty.

Whichever is chosen, the bounds still belong on the `VarDecl`, because the `bound-ints`
pass and any bit-vector profile read them there.

**Implemented** as bounds alone for intervals, an exact range-plus-congruence for
explicit arithmetic progressions, and a membership disjunction for other sparse
domains, except certified bounded-product sets which use the existential
encoding in §2.2. All encodings preserve the exact finite domain.

**Short-table wildcards.** The source meaning of `*` is every value in the declared
domain. This frontend enforces each variable's exact domain in the complete model:
`VarDecl` bounds become target axioms, AP domains become bounds plus a congruence,
and other sparse domains become membership constraints. Therefore a wildcard cell
is a tautology within the whole model and needs no repeated local disjunction. This
optimization is exact for scalar variables, array cells and aliases, including
group/slide expansions; dense-table complementation is disabled whenever a row
contains a wildcard. The C++ structural regression checks that sparse membership
appears once and the table contributes only its non-wildcard factors. Whole-model
XOR tests cover sparse/AP domains, repeated scopes, aliases, groups, slides, and
supports/conflicts polarity.

### 4.5 Multi-objective: the HIR is poorer than the engine

`Hir::ObjKind` is `{ MINIMIZE, MAXIMIZE }` (`include/somtparser/hir/hir.h`), and
`Hir::ConstraintModel` carries a `std::vector<Objective>` (`include/somtparser/hir/hir.h`) with no statement of
how several are combined. XCSP3 says: `lexico` or `pareto`.

The engine already knows the difference. `OPT_KIND`
(`include/somtparser/frontend/objective.h:37-44`) has `OPT_LEX_OPTIMIZE`,
`OPT_PARETO_OPTIMIZE`, `OPT_BOX_OPTIMIZE`, `OPT_MINMAX` and `OPT_MAXMIN` alongside the
single-objective kinds, and `omt_emitter` renders objectives for three dialects
(`src/lowering/omt_emitter.cpp`). So the gap is between the HIR and the engine, not between
this project and the problem.

**Implemented.** `ConstraintModel::objective_combination` carries it, `Uir::Hir::typeCheck`
**requires** it once there are two or more objectives — silence is refused, because silence
was being read as lexicographic — and `omt_emitter` renders `lex`, `pareto` and `box` for
Z3. `minmax` and `maxmin` are this engine's own commands with no Z3 counterpart and are
refused rather than approximated; the SMT-LIB-2025 and OptiMathSAT multi-objective syntaxes
were not confirmed in this pass and are refused for the same reason.

XCSP3-core does not exercise any of it (§1), so this is one of the few places where the
HIR is ahead of the language rather than behind it. The reason is that the requirement came
from OMT rather than from XCSP3: see the note in `include/somtparser/hir/hir.h`.

Retained for the record, because the argument is what justified implementing it rather than
refusing: **flattening a multi-objective set into independent objectives answers a different
question.**
The tempting shortcut — translate the objectives as an unordered list and let the emitter
produce several `(minimize …)` commands — silently answers a different question:

| What the instance asks | What an unordered list of objectives means |
|---|---|
| `lexico`: optimise the first, then the second among first-optima | independent single objectives, or an unspecified order |
| `pareto`: report the non-dominated frontier | a single point |

Both are wrong answers reported as success, which is the failure class
`docs/known-defects-2026-08-11.md` §2 is entirely about. `E_UNSUPPORTED_CONSTRUCT` is the
correct outcome today.

The fix was small and is done: a combination field on `ConstraintModel`, plumbed to the
emitter, which already had somewhere to send it. It was the cheapest genuinely-new HIR
feature in the batch — and XCSP3 is *not* what made it necessary, which is the correction
above: OMT did.

### 4.6 XML is not free

Not a semantic gap, but the practical one that will dominate early effort. XCSP3 is the
only XML format in the batch. That means a dependency (or a hand-written parser), entity
and encoding handling, and a decision about streaming versus DOM (§1). None of it is
interesting, all of it is required, and it is a fair part of why
`docs/languages-scoping.md` §3.2 costs the language at 2.0× despite its semantics being
mostly cluster-A work that other languages pay for too.

---

## 5. New HIR surface this format forces

| Surface | Needed for | Also needed by |
|---|---|---|
| ~~a multi-objective combination~~ — **landed** as `ConstraintModel::objective_combination` (§4.5) | full XCSP3; the requirement came from OMT, not from this language | the OMT arm generally |
| `SortKind::ARRAY` + `ExprKind::ARRAY_ACCESS` | `<array>`, `element`, extension tuple lists | MiniZinc, FlatZinc, Essence′ |
| `Op::ITE` | `count`, `minimum`/`maximum`, `abs`, `if` | FlatZinc, MiniZinc |
| `Op::DIV_TRUNC`, `Op::MOD_TRUNC` | `intension` division (§4.1) | MiniZinc, FlatZinc, Boogie, CryptoLine |
| `Op::ABS` | `abs`, `dist` | MiniZinc, FlatZinc |
| `Op::IMPLIES`, `Op::IFF` | `intension` `imp`/`iff`, `channel` | MiniZinc |
| a global-constraint call form | the whole of §2.3 | all of cluster A |
| ~~`SortKind::SET`~~ **landed 2026-08-12**, `SortKind::ENUM` | full XCSP3 only, **not** XCSP3-core | MiniZinc, Essence′ |
| `ExprKind::COMPREHENSION` | not needed — XCSP3 is ground | (MiniZinc, Essence′ need it) |

The last two rows are the useful ones for planning: XCSP3-core needs **no binder** (unlike
MiniZinc and Essence′) and **no set sort**, so its share of cluster A is the array and
global-constraint half only. Its own contribution is the objective surface.

---

## 6. Fidelity summary

**Exact — the accepted surface.** Integer domains, intension/extension constraints, the
core global catalogue, lifted tuples/matrices, template expansion, and supported objective
orders preserve the source solution relation. `regular`, `mdd`, and `circuit` introduce
witnesses, so their exactness statement includes the recorded `beta` projection.

Fixed-arity extension groups with scalar variable arguments may share one
non-recursive HIR Boolean function. Sharing requires identical declared domains
at corresponding formal positions and an identical alias pattern between actual
arguments. Its body uses the same dense-complement, domain-aware factoring and
direct encoding choices as an expanded table, preserving supports/conflicts,
wildcards, repeated variables and out-of-domain tuples. Other groups retain
ordinary expansion. Generated function/parameter names avoid source symbols,
including equivalent quoted spellings. Helpers stay outside the source-level
observable projection. Only the representative row is retained during preflight;
argument rows are consumed during call construction.

Repeated fixed-arity intension groups can share defined Boolean functions after
specializing integer literals. Independent parameters preserve differing actual
alias patterns; free source variables retain their global scope. Boolean-domain
operands (0..1) have a separate specialization so source Boolean coercions remain
valid. The helper includes the root definedness condition, including selected
branches and nonzero divisors. Sharing is used only when it reduces operator
nodes; variadic groups, compound actual expressions and non-profitable groups
retain ordinary substitution. Compound actuals are not eagerly evaluated, which
preserves partial expressions in guarded branches.

A shared specialization whose closed Boolean body is `P(x) or P(y)` can
compress a complete undirected graph of distinct variable pairs to
`sum(ite(P(x), 0, 1)) <= 1`. The frontend verifies every unordered pair and
structural alpha-equivalence of the two unary predicates after definedness
closure. Duplicate and reversed edges are harmless. Missing edges, self-edges,
asymmetric predicates and scopes above the recognizer's 64-variable budget
retain the ordinary exact encoding. This budget limits only optimization, not
accepted input sizes. Literal specializations are checked independently.

Repeated ordinary extension tables can also share a defined relation, including
tables inside blocks. Eligibility uses the exact supports/conflicts text,
per-position domains (including cell-specific array domains), and alias pattern;
a hash lookup is followed by full comparison. The memo owns its representative
text and removes consumed XML node addresses before temporary group/slide nodes
can reuse them. Unique tables retain the existing lowering path.

**Exact but potentially large.** Extension constraints (§4.2), value-occurrence encodings,
automaton layers, subcircuit positions, and expanded groups/slides can grow substantially.
`cumulative` checks finitely many symbolic event points. It never enumerates the
integer time horizon; larger task lists share their exact load expression.

**Not approximated.** Full-XCSP3 set/real/graph variables and generalized views outside the
declared surface are rejected with diagnostics; the frontend does not silently bound them.

**Ways to make it lossy by mistake** — the four to check for:

- Reading a non-contiguous domain as a range (§2.2, §4.4). **Unsound: admits solutions the
  instance forbids.**
- Encoding `circuit` as only `allDifferent` on successors (§4.3). **Unsound: admits several
  disjoint nontrivial cycles.**
- Converting a `conflicts` table to a `supports` table without the full Cartesian product
  (§4.2). **Unsound.**
- Flattening a `lexico`/`pareto` objective set into independent objectives (§4.5).
  **Answers a different question, and exits 0.**

Three of those four are unsound in the same direction — the translated problem accepts more
than the original — which is the direction that produces a confident wrong SAT.

---

## 7. References

**Format specification**

1. F. Boussemart, C. Lecoutre, G. Audemard, C. Piette, *XCSP3: An Integrated Format for
   Benchmarking Combinatorial Constrained Problems*. <https://arxiv.org/abs/1611.03398>.
2. *XCSP3-core Specification 3.2*. <https://arxiv.org/abs/2009.00514>.
3. Constraint-by-constraint online specification. <https://xcsp.org/specifications/>.

**Competition and corpus**

4. XCSP3 competition series. <http://xcsp.org/competitions/> — per-edition instances,
   rules and results. Instance counts and licence terms **not re-confirmed**.
5. ACE and Choco, the reference solvers; the XCSP3 Java and C++ parsers. URLs, licences and
   versions **not re-confirmed**.

**This project**

5. `docs/languages-scoping.md` §3.1 (cluster A), §3.2 (2.0×), §4 (Plan 2), §1.2/§1.7 (the
   corpus-licence open items).
6. `docs/related-work-round2.md` §3 (the XCSP3-core catalogue count this document expands).
7. `docs/languages/minizinc.md` §4.1 (the `div`/`mod` convention), §4.3 (global-constraint
   decomposition as cluster A's shared work).
8. `docs/languages/flatzinc.md` §4.3 (the `element` encoding, including the index-range
   trap), §4.4 (sets).
9. `docs/languages/dimacs-cnf.md` §4.4 (the memory arithmetic §1 and §2.5 refer to).
10. `docs/known-defects-2026-08-11.md` §2 (the silent-wrong-answer failure class §4.5
    belongs to).
11. `include/somtparser/hir/hir.h`, `include/somtparser/translation/fidelity.h`,
    `include/somtparser/frontend/objective.h`, `src/lowering/omt_emitter.cpp`,
    `test/regression/test_int_div_mod_semantics.cpp`.
