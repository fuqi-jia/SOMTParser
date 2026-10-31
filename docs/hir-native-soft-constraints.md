# Native HIR soft constraints

`HirModel.soft_constrain(expr, weight, *, group="", source_path="")` adds one
weighted Boolean formula. `weight` is a Python string containing a positive
integer in decimal digits. Its precision is unlimited; it is never converted
through `float`. Leading zeroes are canonicalized. Zero, signs, decimal points,
fractions, exponents, whitespace and non-string values are rejected.

```python
from somtparser import _somtparser as native

model = native.HirModel()
p = model.declare("preferred", native.HirSort.boolean())
model.soft_constrain(p, "100000000000000000000000000000001",
                     group="preference", source_path="preferences[0]")
translation = model.translate(dialect=native.OmtDialect.Z3)
assert translation.ok
script = translation.to_smt2(native.OmtDialect.Z3)
```

For each group, the cost of an assignment is the sum of the weights of its
false formulas. A formula contributes its weight once even when it is a
conjunction with several false conjuncts. Repeated calls remain separate
weighted items. Soft constraints do not restrict the feasible assignments;
`constrain` continues to add hard constraints.

`group` is empty for the unnamed group, or a valid SMT-LIB symbol spelling.
Use an explicitly quoted symbol, such as `"|cost with spaces|"`, for spaces.
Invalid symbol syntax is rejected before emission. `"g"` and `"|g|"` denote
the same group. An empty quoted symbol is rejected to avoid confusion with
the unnamed group.

The effective objective vector consists of distinct soft groups in their
first-appearance order, followed by explicit arithmetic objectives in their
model order. Calling `objective` before `soft_constrain` does not interleave
their emitted commands. Two or more effective objectives require an explicit
combination, for example `model.objective_order("lexicographic")`. This native
Python entry point currently exposes `single` and `lexicographic`; C++ retains
its existing combination enum.

Grouped or mixed multi-objective soft models require the Z3 output dialect.
Other dialects report an unsupported combination rather than silently omit
its priority. Single soft groups retain the existing `assert-soft` output.
Native `Constraint.weight_text` has the same positive-integer contract. The
existing C++ `double weight` fallback remains available but is not used by
this exact Python interface.

The cost and grouping interpretation follows the
[Z3 soft-constraint documentation](https://microsoft.github.io/z3guide/docs/optimization/softconstraints/)
and [objective combination rules](https://microsoft.github.io/z3guide/docs/optimization/combiningobjectives/).
This entry point constructs typed HIR; it makes no claim about natural-language
intent. JSON/`hir.py` integration is a separate interface change.
