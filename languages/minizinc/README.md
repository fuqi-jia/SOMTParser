# MiniZinc

## Overview
MiniZinc is a solver-independent constraint modelling language from Monash
University and Data61. Specification: https://docs.minizinc.dev/

## Entry point
- C++: `SOMTParser::Lang::mkMiniZincLanguage()` from
  `<somtparser/languages/minizinc.h>`
- Conversion API: `somtparser.translate("model.mzn")`
- Python: `somtparser.translate("model.mzn")`

## Input model
A `.mzn` file, the model files it `include`s, and any `.dzn` data files passed
alongside it. `MiniZincLanguage::acceptsDataFiles()` returns `true`, so
`Uir::translate` hands `data_paths` to the frontend rather than refusing them.

A MiniZinc model is not one file and **its items are not ordered**: every
instance file in libminizinc's examples is an `include` followed by the
assignment the included model already used, so `n` is read in `array[1..n]`
before `n = 3;` appears. The value is needed at *parse* time — the index set
decides how many variables are declared — so there is an assignment pre-pass
before the real parse. Include paths resolve against the including file's
directory; a cycle is refused by name and so is a chain more than 32 deep.

A `.dzn` may contain assignments and nothing else. A `constraint` hiding in one
is refused rather than parsed, because dropping it would make the instance
weaker than the files say.

## Coverage
| Construct | Status |
|---|---|
| `var int:` / `var bool:` declarations | supported |
| integer range domains `var l..u:` | supported, emitted as two assertions |
| `constraint` items | supported |
| `solve satisfy / minimize / maximize` | supported |
| `--dialect none` on optimization | feasibility-only; requires profile `feasibility` (or another floor permitting objective loss) |
| arithmetic `+ - *`, comparisons, `/\ \/ not` | supported |
| `div`, `mod` | supported, as `Op::DIV_TRUNC` / `Op::MOD_TRUNC` (`docs/languages/minizinc.md` §4.1) |
| partial expressions | supported for dynamic `div`/`mod` and array access through `Uir::Sem::RelationalBuilder`; guards close at Boolean scope |
| `array[l..u] of ...`, one index set | supported |
| parameter arrays, from the model or from a `.dzn` | supported |
| decision-indexed parameter arrays | shared typed constant arrays, with per-dimension bounds and per-read definedness; initializer holes retain decision values |
| `nvalue` over finite integer/enum arrays | exact distinct count using a linear shared array DAG; all input definedness is retained |
| `var set of int` / `var set of l..u`, `in`, `subset`, `card`, set literals | supported |
| `predicate` items | supported, inlined at each call site |
| generator calls — `forall(i in S)(...)`, `sum`, `alldifferent(i in S)(...)` | supported |
| `include`, of a model file or a standard-library name | supported |
| annotations | parsed and skipped, with a note — they do not change declarative semantics |
| global constraints | read, and decomposed — but only under a profile whose pipeline runs `decompose-globals`; see below |
| par `set of int: S = ...;` items and `union` | supported as canonical disjoint integer intervals |
| multi-dimensional index sets — `array[S1, S2] of ...` | supported, **flattened row-major**; see below |
| `alldifferent` and its `all_different` spelling | supported; both are in `globals.mzn` |
| `var float`, fixed float parameters/literals, float arrays/predicate parameters, and `/` | supported as exact SMT `Real`; decimal/scientific/hex constants are exact rationals |
| finite list comprehensions used as decision-array initializers — `[e \| i in S where c]` | supported; expanded in source order with relational definedness |
| inferred decision arrays — `array[int] of var T: a = [...]` | supported as source index set `1..length(a)` |
| fixed parameter-set comprehensions — `set of int: S = {e \| i in R where c}` | supported as canonical disjoint integer intervals; sparse domains retain holes |
| collection values in other expression positions | `E_UNSUPPORTED_CONSTRUCT`; require first-class list/set terms |
| several generator variables over one set — `forall(i, j in S)` | supported |
| named integer domains — `var sq: x`, `array[R] of var sq: a`, `predicate p(row: r)` | supported as Int plus explicit domain checks |
| array-valued predicate parameters | `E_UNSUPPORTED_CONSTRUCT`; the caller's source index set must be carried |
| a parameter set with a hole — `{1, 3}` | supported as a value/generator domain; refused as an array index set |
| `output` items | parsed and skipped, with a note — they say how a solution is printed |
| `function`, `test`, `enum`, `annotation`, type-inst synonyms | `E_UNSUPPORTED_CONSTRUCT` |

**Two index sets are flattened row-major**, and that decision is recorded as an
`EncodingChoice` (`array-flatten-row-major`) because nothing in the emitted
script preserves it: a flattened `array[1..2, 1..3]` and a plain
`array[0..5]` produce identical SMT-LIB. The map is a bijection, so the
translation stays `exact()`. Bounds are checked **per dimension, before
flattening** — `a[2, 4]` on `array[1..2, 1..3]` flattens to 6, an ordinary
in-range index denoting a cell of a third row that does not exist, so a check
applied after flattening would accept it.

A parameter set is represented as canonical **disjoint integer intervals**.
Holes are exact for value domains and generators. A set with a hole (`{1, 3}`)
is refused only when used as an array index set: widening it would add indices
the model never declared, and every one of them is a select into the total
function's unconstrained part.

**A global constraint is read by this frontend and eliminated by a pass, so
whether it translates is a property of the profile.** `alldifferent` becomes
`Hir::Global`, carrying the `global-constraint` feature, and
`decompose-globals` eliminates it. That pass is in **all seven**
built-in profiles, so the choice a profile expresses is between encodings and
never between answering and refusing.

This is worth stating because it was wrong the other way for a while, and
invisibly: `default` — the profile the CLI uses when given no flag — had an
empty pipeline, so **every** model containing `alldifferent` was refused, and
the upstream corpus read 1 of 16 under `default` against 2 of 16 under
`ground`. No coverage table could show it. The frontend had read the construct
correctly; the refusal happened a layer above, which is a layer no
per-language number describes.

### `OpCoverage` numbers: derivation and caveat

`MiniZincLanguage::coverage()` reports `total = 21`, `supported = 19`, and a
two-entry `missing` naming first-class collection comprehensions and array-valued
predicate parameters. The counts and the list are
kept in agreement (`missing.size() == total - supported`), and a test asserts
that rather than asserting the numbers, so the invariant survives the next
change to them.

**The number grew twice, both times for the same reason.** It began at 10 —
what this subset was *designed* to target, which is a subset measured against
itself and therefore reports full marks. Running libminizinc's own examples
took it to 16, and the remaining corpus failures took it to 21. A construct
the format's authors actually write has to be counted whether or not this
frontend reads it; leaving it out is how a table reads 9 of 10 while the
corpus reads 0 of 16.

**`missing` is emptied when a construct can be used, not when a line of code
mentions it.** `/` left the list only when `var float`, exact constants,
parameters, arrays and predicate arguments could all carry its result. The same
rule caught the table reading 8/8 while `x div 2` was refused.

**It can be wrong in the other direction too, and that is harder to notice.**
`.dzn` data files and multi-file `include` sat in `missing` for a day after
both had landed, because nothing fails when a table under-reports.

**What this count deliberately excludes**, so it does not read as more
authoritative than it is: it does not tally expression-level `Hir::Op` values
individually, and it does not include every keyword the parser refuses —
`function`, `test`, `enum` and `annotation` are refused with
`E_UNSUPPORTED_CONSTRUCT` (see `mzn_minimal.cpp`'s item dispatch) without
appearing in `missing`. Counting those would change both `total` and
`missing` without changing `supported`.

**This is a per-language, ad hoc item count, not a measurement against a
canonical unified-ops catalog** — no such catalog exists yet in this
project for `OpCoverage` to be reconciled against. Treat `total`/`supported`
as a coarse indicator of this frontend's grammar breadth, not a finished
coverage figure; it should be recomputed once a real ops catalog and a shared
counting convention exist, at which point `function` and `test` will also need
a decision on whether they belong in `missing`.

**And it is bounded from both sides.** It cannot count a construct the engine
below it cannot represent, and it cannot see a construct the *pipeline* above
it refuses — the corpus difference between `default` and `ground` is entirely
the second kind. A frontend's coverage number is a statement about one layer.

## Semantic gaps
Under the `default` and `strict` profiles the supported subset maps exactly, so
translations report `sound = complete = true`.

There is already one gap, and it comes from the profile rather than from the
grammar: under **`bv32`** the `bound-ints` pass clamps every otherwise-unbounded
`var int:` to the signed 32-bit range. That keeps found solutions real
(`sound = true`) while excluding solutions outside the range, so the report
reads `complete = false`, `preserves_optimum = false`, with a
`Bound{BV_WIDTH, 32, site}` per clamped variable and one `EncodingChoice`
recording the decision. See `test/python/test_translate.py`
(`test_bv32_profile_bounds_unbounded_ints_with_incomplete_fidelity`) and
`test/translation/test_uir_translate_e2e.cpp`.

A second difference between profiles is not a fidelity loss at all. Both
decompositions of a global constraint are `exact()` — they differ in output
size and in how a solver behaves, not in what they preserve — so the choice
between them is carried by `EncodingStyle` rather than by the fidelity floor,
and picking one does not weaken the result. A profile that runs neither does
not approximate the model either; it refuses it.

## Encoding options
None specific to this language, but the shared profiles are **not
interchangeable** for it:

| Profile | On a MiniZinc model |
|---|---|
| `default`, `strict` | exact; decomposes globals into ground constraints |
| `ground` | exact; the same, stated in the profile's name |
| `quantified` | exact; decomposes globals using quantifiers instead |
| `bv32` | decomposes, then clamps unbounded `var int:` to signed 32 bits; `complete = false` |
| `bmc` | decomposes; `complete = false`, for a bound the frontend supplies |
| `feasibility` | decomposes and permits `--dialect none` to retain only the feasible set; `preserves_optimum = false` |

**Every built-in profile decomposes global constraints**, so no profile decides
whether a model is *answerable* — only how it is encoded. `bv32` runs
`decompose-globals` before `bound-ints`, which makes no difference today
(`bound-ints` walks declarations and the ground decomposition adds none) and is
ordered that way for the encoding that does introduce variables: the profile
promises every unbounded Int is clamped, and a pass that ran after the clamping
would produce ones that are not, while the report still carried the bound.

The ground encoding enumerates the index range, so an `alldifferent` whose
bounds are not literals is refused under `default` with a message pointing at
`quantified`. Use `quantified` for those, and for models where the pairwise
expansion would be too large.

## Known limitations
Collection-valued expressions outside fixed parameter-set and decision-array
initializers, and array-valued predicate parameters are refused rather than approximated.
Non-contiguous parameter sets also cannot be array index spaces in the current
HIR. See the coverage table above and
`docs/languages/minizinc.md` §4 for what each would cost.

## Test instances
- `instances/ok/` — must translate successfully
- `instances/ok/multifile/` — the `include` and `.dzn` fixtures. Some of these
  must *fail* (a cycle, a missing include, a short data array); they live here
  because each is one half of a multi-file pair whose other half must succeed,
  and splitting the pairs across directories would hide the pairing.
- `instances/reject/` — must fail with a specific `ErrorCode`
- `instances/upstream/` — libminizinc's own examples, unmodified. See
  `PROVENANCE.md`. These are a measurement, not a target: most do not
  translate, and which ones fail on what is the point.

## References
- MiniZinc Challenge: https://www.minizinc.org/challenge.html
- Prior art targeting SMT: fzn2smt (SAT 2010), FZN2OMT (CPAIOR 2020),
  Savile Row's SMT backend (CP 2020)
