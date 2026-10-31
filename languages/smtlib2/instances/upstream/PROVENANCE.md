# Upstream corpus — SMT-LIB 2

Unmodified `.smt2` files from **cvc5**, `test/regress/cli/regress0/` — the eight
smallest from each of six theory directories: quantifiers, arrays, bv, strings,
datatypes and sets.

- Source: https://github.com/cvc5/cvc5/tree/main/test/regress/cli/regress0
- Retrieved: 2026-08-17
- Licence: modified BSD (cvc5 authors and contributors). GitHub reports the
  repository as `NOASSERTION` because `COPYING` opens with prose before the
  licence text; the terms are 3-clause BSD and permit redistribution.
  Unmodified.

Sampled by theory rather than by size alone, because this frontend's surface is
the whole of SMT-LIB and a corpus drawn from one directory would report on one
theory. `test/instances/` already held 21 scripts, but those are **this
project's** files: written against this parser, so they can only find what
someone here thought to write down.

## First run: 40 of 48, now 41

The one that mattered was in the ENGINE, not the frontend, and it took a corpus
of someone else's files to reach it.

**`str.to_int` failed on every string literal**, including `(str.to_int "7")`.
Two defects in one case:

- It read `toString()`, which renders a string constant **with its quotes**, so
  the is-it-digits test saw `"7"` rather than `7` and no literal ever took the
  folding branch. `getStringLiteral()` is the accessor for the value, and
  `str.len` two cases above was already using it.
- It then **raised an error** for a non-numeric string. SMT-LIB defines
  `str.to_int` total: a string that is not a run of digits maps to **-1**, so
  `(str.to_int "abc")` is a well-formed term and erroring turned a legal script
  into a parse failure.

`str.to_code` had both, `str.is_digit` and `str.rev` had the quoting one. And a
neighbour check written to confirm the fix was not too narrow found a fourth:

**`(= (str.from_int 7) "7")` folded to FALSE.** Nodes are hash-consed by name,
and `mkConstStr` stored a quoted argument with its quotes and an unquoted one
without — so a constant built through the API and the identical literal read
from a script were never the same node. Both *printed* as `"7"`, because
printing adds the quotes when they are missing, so the disagreement was
invisible in the output and surfaced only as an equality that would not hold.
That is PR #52's symbol-identity defect, one sort along.

**Why the operator sweep missed all of it**:
`test/lowering/test_lift_operator_sweep.cpp` covers every one of these
operators, and covered them while they were broken. It exercises each over a
declared VARIABLE, which is right for a lift-and-lower round trip and reaches
none of `simp_oper`'s constant folding — folding only fires on a constant. The
sweep and the folder are disjoint by construction, and
`test/regression/test_string_const_folding.cpp` now covers the gap.

## What the remaining seven are

Three are `Tuple` sorts, refused by name — no HIR counterpart.

Four are refused with the **engine's own message and no `ErrorCode`**:
`declare-codatatypes`, bare `set.empty` and `set.is_empty`, and
`nullable.some`. Bare `set.empty` is cvc5's spelling — SMT-LIB writes
`(as set.empty (Set Int))`, which this parser reads fine — and `set.is_empty`
and `nullable.some` are cvc5 extensions, so refusing all three is correct under
the scoping rule of open-questions D26. `declare-codatatypes` is real SMT-LIB
and is a genuine gap. What is wrong in all four is the *shape* of the refusal:
a raw engine message reaching the user with no code attached, which is the same
class MoXI's PROVENANCE.md names.
