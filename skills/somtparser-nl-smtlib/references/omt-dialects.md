# OMT dialects: solver syntax versus implemented route

Optimization extensions must name their target dialect. A solver's capability
does not imply that every SOMTParser frontend/model API exposes it.

| Feature | Z3 syntax | OptiMathSAT syntax | Pure SMT-LIB route |
|---|---|---|---|
| Numeric objective | `minimize` / `maximize` | `minimize` / `maximize` | Optimization rejected, never erased |
| Soft preference | `assert-soft` with weight/group | Documented `assert-soft` extension | Rejected unless an explicitly different source task was requested |
| Multiobjective priority | `:opt.priority lex`, `pareto`, `box` | Official examples use `lex`, **`pareto`**, `box` | No optimization command |
| Model/result query | Result-dependent | Box may require `load-objective-model` to select a model | Result-dependent |

Current HIR JSON exposes single/lexicographic order; it does not expose a generic
Pareto/box field. The inspected native OptiMathSAT emitter rejects multiobjective
combination. Retain that diagnostic until implementation and backend validation
exist. Do not emit a guessed `par` option or claim those routes tested.
The direct formal candidate prohibits `set-option`, so it also cannot bypass
that restriction by putting priority options in provider text.

Bounds annotations are not a license to change a feasible set. No range is added
to prevent infinity. A strict Real bound may produce an unattained infimum; adding
an epsilon or rounding to an integer changes the problem. Never promise a finite
attained optimum from translation alone. Keep exact costs and priority order.

Sources checked during this revision:

- [Z3 objective combinations](https://microsoft.github.io/z3guide/docs/optimization/combiningobjectives/)
- [OptiMathSAT official examples](https://optimathsat.disi.unitn.it/pages/smt2examples.html)
- Repository `src/lowering/omt_emitter.cpp` and public `OmtDialect` binding.

SMT/OMT proposals or the repository's `SmtLib2025` dialect are not treated as a
universal deployed OMT standard. This skill's `smtlib-pure` maps to the explicit
no-optimization dialect.
