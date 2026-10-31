# Upstream corpus — MiniZinc

Unmodified files from **libminizinc**, `tests/spec/examples/`.

- Source: https://github.com/MiniZinc/libminizinc/tree/master/tests/spec/examples
- Licence: MPL-2.0 (Monash University, NICTA / Data61). Retained here under the
  notice requirement of that licence; the files are unmodified.

The first run over these was 0 of 16, **every one failing at line 1, column 1**
on the same character: they open with a `/* ... */` licence header and this
lexer knew only `%`. A uniform failure at the first token is never a semantic
gap. That one fix moved the whole failure distribution deeper and made the next
three gaps visible -- parameters, `->`, and `include` -- which is what a corpus
is for.

The four `.model` files are vendored alongside the instances that include them,
because an instance file without its model is not a smaller problem -- it is
nine lines of data.

As of 2026-08-25, 7 of 16 translate. The sixth is `golomb.mzn`: exact finite
array-comprehension expansion and value-derived `array[int]` indexing expose its
six ordered differences without adding a first-class collection value to HIR.
The seventh is `perfsq2.mzn`: a fixed set comprehension is retained as disjoint
integer intervals, and its sparse named variable domain lowers to exact
membership rather than the unsound interval from its minimum to maximum.

`include` and the assignment pre-pass then moved the distribution again, and
this is what a corpus is for: not one of the sixteen counts as translated that
did not before, and every one of them now fails on something DEEPER. Eight on
`set` items, three on two-dimensional index sets, one on annotations, one on a
parameter array from data, one on `int` used as an identifier. A count that had
not moved would have looked like no progress; the reasons are the progress.
