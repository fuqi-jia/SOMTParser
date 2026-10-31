# Upstream corpus — FlatZinc

Unmodified files from **libminizinc**, every `.fzn` under `tests/` (43 of the 44
there; one is empty).

- Source: https://github.com/MiniZinc/libminizinc/tree/master/tests
- Retrieved: 2026-08-17
- Licence: MPL-2.0 (Monash University, NICTA / Data61). Retained here under the
  notice requirement of that licence; the files are unmodified.

These are **compiler output**, which is what makes them the right corpus for
this format. FlatZinc is not written by hand — it is what `minizinc -c` emits —
so a file produced by the reference compiler is the format as its authors
actually produce it, including the annotations, the introduced variables and the
solver-specific builtins that a hand-written sample would never contain.

## First run: 22 of 43

And the failures were more interesting than the count. Two of them were **wrong
error codes rather than missing features**, and both were invisible until a
corpus existed to contain them:

- **`E_PARSE: undeclared identifier '1.0'`** on `float_inf_range_dom.fzn`.
  `var float` already mapped to `Sort::real()`, so the SORT was supported and
  the LITERAL was not — a number was being reported as a variable the model
  forgot to declare. Half a theory, filed as malformed input. Fixed; the file
  now reaches `array_bool_and`, an honest gap.

- **`E_PARSE: 'y' is not an array`** on the four `optimization_*.fzn` files,
  each containing `var set of {1,3,5,7,9}`. `set_in` had *already* identified
  this correctly and reported `E_UNSUPPORTED_CONSTRUCT` — and was defeated by
  ORDER, because `arrayItems` filed an `E_PARSE` first and `firstErrorCode()`
  takes the first. The frontend knew the right answer and could not say it.

After both, **every one of the twenty-one refusals is
`E_UNSUPPORTED_CONSTRUCT`** and none is `E_PARSE`. That matters more than the
22: `E_PARSE` and `E_UNSUPPORTED_CONSTRUCT` feed different statistics —
"malformed input" against "coverage gap" — so a mis-bucketed refusal corrupts
the failure-cause distribution this corpus exists to produce.

## What the twenty-one are

Almost all are unimplemented builtins, which is the honest shape of FlatZinc
coverage: the builtin catalogue is **open**, and solvers extend it. Among them
are `gecode_table_int`, `gecode_int_element`, `chuffed_blackbox`,
`chuffed_blackbox_bounds` — solver-specific names no general reader can be
expected to know — and `my_pred`, `foo`, user-defined predicates from the
compiler's own test models. A frontend cannot close that set, only refuse
unknown names by name, which it does.

The rest: `array_bool_and`, `array_int_minimum`, `array_int_lt`, `fzn_count_eq`,
`int_le_imp`, `int_eq_imp` (the half-reified `_imp` family), `set_in` over a set
variable, and one `0.0..1.0` float domain.
