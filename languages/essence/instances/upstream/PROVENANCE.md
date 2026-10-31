# Upstream corpus — Essence′

Unmodified `.eprime` files from **Conjure**, `tests/exhaustive/`.

- Source: https://github.com/conjure-cp/conjure/tree/main/tests/exhaustive
- Retrieved: 2026-08-17
- Licence: BSD-3-Clause (Özgür Akgün, School of Computer Science, University of
  St Andrews). GitHub reports the repository as `NOASSERTION` because the notice
  is hand-written rather than a verbatim template; the terms are BSD-3-Clause
  and permit redistribution with the notice retained. The files are unmodified.

24 of the 2220 there, sampled across the size range and one per test directory —
a corpus, not a mirror. Each is named after its originating test case rather
than the `model.eprime` all 2220 share.

These are **Conjure's output**: Essence′ is what Conjure produces from Essence,
so these are the format as its own toolchain writes it — the mangled
representation names (`var1_PartitionAsSet_ExplicitVarSizeWithMarkerR6_Marker`),
the `branching on` directives and the deeply nested comprehensions that a
hand-written sample would not have.

## First run: 0 of 24, and fifteen on one token

Every one of those fifteen was `E_PARSE: unexpected 'branching'`.

**A uniform failure on one token across most of a corpus is never a semantic
gap.** It is the same shape as MiniZinc's corpus failing 16 of 16 at line 1
column 1 on a comment syntax the lexer did not know, and it is the reason to run
a corpus before trusting a coverage table.

`branching on [x, y]` and `heuristic static` state a **search order**. They
select which variable a solver tries first and leave the set of solutions
unchanged, and this frontend emits constraints rather than a search strategy —
so they are skipped with a note, which is the reading MiniZinc's annotations
already get. Skipping is safe *because* the semantics are declarative, and it is
reported rather than silent because "this frontend ignored something the file
said" is a fact the reader is entitled to.

## Where it stands: 12 of 24

It was 0 on the first run and 2 after `branching` was skipped rather than
refused. The distribution mattered more than the count at every step, and the
step that finally moved it is the fold below.

Two wrong codes were found and fixed along the way:

- **`E_TYPE: 'and' is not declared`** on twelve files. `and([...])` and
  `or([...])` are Essence′'s n-ary folds over a comprehension — the language
  defines them — so a name the *format* provides was reported as one the *model*
  forgot to declare. Now `E_UNSUPPORTED_CONSTRUCT`, alongside the rest of the
  operator catalogue.
- **`E_PARSE: unexpected '<->'`**. Bi-implication was *lexed* and never parsed,
  so a legal operator read as unexpected punctuation the lexer had just
  recognised. Implemented: there is no `Op::IFF`, and on two Booleans `EQ` is
  exactly bi-implication.

**`and([ body | q : D ])` is a COMPREHENSION FOLD**, and implementing it took the
corpus from 2 to 12. It is `quantified()` with the generator written after the
body rather than before, so the expansion is identical and the only new work is
finding the `|`: the body has to be skipped before its generators can be read,
then re-parsed once per tuple. `toInt` — Essence′'s explicit Bool-to-Int
coercion, which Conjure emits wherever a Boolean is summed — came with it, and is
`ite(b, 1, 0)`: the coercion itself, not an encoding of it.

One defect in the fold is worth recording because nothing about it looked wrong.
The fold's `kind` was taken as a `const std::string&` bound to the caller's
`tok_.text`, and the first `eat()` overwrites the current token — so `kind` named
whatever token came next, every comparison against `"and"` and `"or"` failed, and
every fold silently became a `sum`. The symptom was
`argument 1 of '+' is Bool, not numeric`: a conjunction of Booleans added
together. **A dangling reference produced a well-typed wrong answer**, and the
error it raised pointed at arithmetic rather than at the fold.

What remains: multi-dimensional matrices (4 files), three files that need their
`.param` which this sweep does not pass, and one out-of-range index.

## Update on 2026-09-21 — the three missing `.param` files

Three `.eprime` files here are **parameterised models**, and their parameter
files were never vendored alongside them:

| model | parameter file, as vendored | from |
|---|---|---|
| `basic_toSet_comprehension.eprime` | `basic_toSet_comprehension.param` | `tests/exhaustive/basic/toSet_comprehension/n4.param` |
| `basic_powerSetComprehensionDirect.eprime` | `basic_powerSetComprehensionDirect.param` | `tests/exhaustive/basic/powerSetComprehensionDirect/p.param` |
| `issues_168.eprime` | `issues_168.param` | `tests/exhaustive/issues/168/p.param` |

Same repository, same licence, unmodified; retrieved 2026-09-21. Renamed to the
model's own basename because that is what `scripts/sweep-corpora.sh` pairs on —
the originals are `p.param`/`n4.param` inside per-test directories, and every
file here is already renamed away from the `model.eprime` all 2220 share.

`toSet_comprehension` ships two parameters (`n4`, `n5`); one model serves both,
and `n4` is the one vendored. Taking one of several parameter files is a
sampling decision, so it is recorded rather than left to the filename.

**Without them the refusal was `parameter 'n' has no value` — a true statement
about an incomplete invocation, filed as a coverage gap.** That is the
mis-bucketing class this corpus exists to expose, one level up: not the wrong
error code for a construct, but a correct code for a question nobody asked.
With the parameters supplied all three move deeper and fail on named
constructs instead — `catchUndef`, a `matrix` domain where an `int` was
expected, and `flatten` — which is the useful shape (D23).

## Update on 2026-09-22 — 20 of 24

`alldifferent_except`, a lowered `<lex` (over decision-variable elements, not
just the parse-time constants the guard path reads), `flatten`, `allDiff` over
an explicit list, `min`/`max` over one, and the symbolic `/` and `%` landed —
each a few lines on top of separating the comprehension's element expansion
from the FOLD over those elements.

The four that remain are one construct each: a
generator whose domain is a *matrix* — higher-order, quantifying over a
function space — and `basic_set07.eprime`, whose comprehension indexes
`x_Occurrence` at 5..9 on a matrix declared `int(1..4)`.

That last one is **not a parser gap and not a coverage gap**: it was put to
Savile Row on 2026-09-22 and the answer is that Savile Row has no consistent
one. With the index out of range, `and([!(m[q] = 3) | ...])` is SAT and
`and([m[q] != 3 | ...])` is UNSAT — two spellings of one formula, and both SAT
when the index is in range. Its handling is a normalisation artifact rather
than a semantics, so refusing with `E_TYPE` naming the index is correct, and
this file counts as a designed refusal. The full bisection is in the 2026-09-22
entry of `docs/continuation-worklog-2026-09-18.md`.

## Correction on 2026-09-23 — relational undefinedness implemented

The 24 unchanged source units now all translate. `basic_set07` was incorrectly
classified as invalid: Savile Row manual 1.11.1 section 3 explicitly defines the
relational undefinedness it uses. The frontend's global definition constraints
were too strong. Local guards now close at the nearest source Boolean node;
Boolean matrix reads are themselves Boolean boundaries. Savile Row/Minion and
the corrected target agree on the original solution, and 39 independent source
probes agree. See `docs/languages/essence-prime.md` and the 2026-09-23 evidence.
