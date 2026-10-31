# CHC-COMP: constrained Horn clauses

**Audit date**: 2026-08-25
**Status**: implemented in `languages/chc/`; accepted inputs have an exact
SMT/OMT embedding.
**Normative format**: [CHC-COMP Benchmark Format, revision 2023-03-31](https://chc-comp.github.io/format.html),
a restricted SMT-LIB 2.6 script.

<!-- implicit-constraints:
  a CHC rule's quantified variables => its clause is universally closed; replacing them with free target constants changes a rule into one ground instance
  every declared Bool-valued relation => a first-class source-model interpretation, including nullary relations; dropping relation interpretations makes beta unable to reconstruct a source model
  a false-headed final rule => the reachability query encoded as a Horn clause, not a source assertion that `false` already holds; the complete rule set is nevertheless asserted directly for satisfiability
  `set-logic HORN` => the official command and clause normal forms still apply; accepting an arbitrary SMT-LIB script under that logic name would claim CHC-COMP semantics for a different language
  background operators and sorts => retain their declared SMT-LIB theory semantics; treating them as uninterpreted symbols changes the constraint relation
-->

## Source Language Boundary

The frontend accepts the official command sequence:

```text
set-info*; set-logic HORN; set-info*; declare-datatypes*;
declare-fun+; assert+; check-sat; exit?
```

Every `declare-fun` must return `Bool`; a zero-argument declaration is a
nullary predicate. There is exactly one false-headed query and it is the final
assertion. Predicate applications take quantified variables only, and head
arguments must be distinct. Arbitrary SMT-LIB scripts carrying `set-logic HORN`
are therefore not silently treated as CHC-COMP benchmarks.

The official background-theory tracks include integer and real arithmetic,
arrays, bit-vectors and algebraic datatypes. These all use the common typed HIR.
`HORN` constrains clause shape rather than selecting one background theory, so
the core parser enables all theories and the CHC frontend performs the shape
check.

The 2025 BV corpus also contains Z3's `bvudiv_i`, `bvurem_i`, `bvsdiv_i`,
`bvsrem_i` and `bvsmod_i` hardware-interpretation spellings. Z3 defines these
as the corresponding total operations with fixed divisor-zero results. Those
results are the public SMT-LIB 2.6 semantics, so the frontend canonicalizes the
spellings exactly and records an `EncodingChoice`; it does not treat arbitrary
unknown functions as builtins.

## Optimization Institution

For signature `Sigma`, the source institution is:

```text
Sign  = background sorts/functions plus Bool-valued predicate signatures
Sen   = universally closed constrained Horn rules and one query
Mod   = background-theory structures plus an interpretation of each predicate
|=    = every universal closure evaluates to true
Cost  = none
Order = satisfaction only
Obs   = verdict plus declared predicate interpretations
```

A CHC model is not merely a valuation of clause variables. It supplies a
relation of the declared arity and sorts for every predicate. Quantified
variables are local to sentences and never become model observables.

## Translation Construction

The implemented adapter is
`T = (Phi, A, alpha, beta, h)`:

| Component | Implementation |
|---|---|
| `Phi` | Identity mapping for accepted sorts, interpreted symbols and predicate signatures |
| `A` | No encoding axioms; background theories retain SMT semantics |
| `alpha` | Preserve each universal Horn clause and false-headed query |
| `beta` | Read each target function interpretation as the corresponding source relation |
| `h` | Trivial, because CHC-COMP has no objective |

For every target interpretation `N`:

```text
N |= alpha(Gamma)  iff  beta(N) |=_CHC Gamma
```

This is an exact embedding for accepted theory terms. In first-order SMT model
semantics, interpretations of declared nonlogical predicates are chosen as part
of the model. Therefore no explicit second-order quantifier and no Horn
unrolling are needed: asserting the unchanged clauses asks whether a suitable
predicate interpretation exists. The all-true interpretation does not make a
general benchmark trivially satisfiable because it must also satisfy the
false-headed query.

## Verdict and Projection

Result polarity is preserved:

| Target result | Source meaning |
|---|---|
| `sat` | A predicate interpretation satisfying every rule and query exists |
| `unsat` | No such interpretation exists |
| `unknown` | No semantic conclusion |

For program-safety encodings, `sat` conventionally means that an inductive
invariant exists. This safety reading is an application of CHCs, not a reversal
of SMT satisfiability.

`ModelProjection` records every declared relation, including nullary ones, and
omits quantified variables. A target solver's textual function definition may
be carried as the observable value; it denotes the whole relation rather than
one application.

## Refusal Policy

The frontend rejects constructs whose acceptance would mislabel another SMT
problem as a CHC-COMP problem: wrong command order, `declare-const`, non-Boolean
functions, existential clauses, disjunctive or interpreted heads, predicates
under non-conjunctive body connectives, term-valued predicate arguments,
duplicate head variables, missing/multiple queries, and commands after
`check-sat` other than optional `exit`.

Exact semantic translation does not imply that every general SMT solver will
solve recursive Horn clauses efficiently. Solver strategy is operational
metadata and does not change `Mod` or `|=`.

## Verification

```bash
cmake --build build --target test_chc test_semantic_contract_coverage
./build/test/test_chc
./build/test/test_semantic_contract_coverage
```

Fixtures cover linear and non-linear bodies, quoted symbols, nullary predicates,
ADTs, command grammar and every normal-form rejection above.

An external audit at CHC-COMP 2025 benchmark commit
`ddd279cab0717db6effe69baad451a8eb04ffd86` translated one selected instance
from each of `ADT-LIA-Arrays`, `ADT-LIA`, `BV`, `LIA-Arrays`,
`LIA-Lin-Arrays`, `LIA-Lin`, `LIA`, and `LRA-Lin` (8/8). The corpus is not
vendored because its repository does not state redistribution terms.

## References

- [CHC-COMP 2025 benchmark repository](https://github.com/chc-comp/chc-comp25-benchmarks)
- [SMT-LIB FixedSizeBitVectors theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
- [Z3 hardware-interpretation remainder implementation](https://github.com/Z3Prover/z3/blob/006525881e9a161b6033da596a347975c4c6f0de/src/ast/rewriter/bv_rewriter.cpp#L1232)
