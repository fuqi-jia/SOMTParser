# Upstream corpus — LP

Unmodified files from HiGHS `check/instances/` (all 18 `.lp` files).

- Source: https://github.com/ERGO-Code/HiGHS/tree/master/check/instances
- Retrieved: 2026-08-17
- Licence: MIT (HiGHS developers, University of Edinburgh)

HiGHS is a reader as well as a solver, so this directory intentionally mixes
valid models, malformed-input tests, and unsupported extensions.

## Audit on 2026-08-25

The frontend accepts **8/18**: `1451`, `2122`, `fixed-binary`, `issue-2388`,
`issue-2585`, `no-newline-eof`, `semi-continuous`, and `semi-integer`.

Six files (`qcqp`, `qjh`, `qjh_uncon`, `qpinfeasible`, `qptestnw`, and
`qpunbounded`) use quadratic syntax. They were valid LP but outside the then
6/9 linear subset and returned `E_UNSUPPORTED_CONSTRUCT`.

## Update on 2026-09-20 — quadratic expressions implemented

**14/18**, which is every valid file: all six quadratic instances translate
(`lp.md` §4.5), and the four that remain are the malformed ones below.

`qjh.lp` and `qjh_uncon.lp` are the useful pair. HiGHS ships the same two
models as `qjh.mps` and `qjh_uncon.mps`, and the two formats state the
quadratic part in unrelated ways — LP writes the coefficients out and divides
the bracket by two, MPS gives a triangle of the Hessian and leaves the 1/2
implicit in the format. `test_lp_quadratic.cpp` requires both frontends to emit
the same objective, which no consistent misreading of either convention can
satisfy. `qcqp.lp` is the other oracle: it carries a divided objective and an
undivided quadratic constraint in one file, so it separates "read the divisor"
from "assume it".

Four files are malformed CPLEX LP and are correctly rejected: `1448` has no
objective section; `1449a` and `1449b` put incompatible sections on one line;
`garbage` is arbitrary text. CPLEX 22.1 rejects the same inputs.

`2122.lp` is a useful semantic oracle boundary. CPLEX accepts a roughly
`-1.96e-11` bound violation under its feasibility tolerance. Exact rational
SMT derives `x623 = -2000/102294058333333` and `x623 >= 0`, so the mathematical
model is UNSAT. This is an operational solver-tolerance difference, not a
reason to weaken the source satisfaction relation.

## Correction on 2026-09-23 — reader variants and keyword labels

The earlier claim that all four refusals were inherently malformed was too broad.
Gurobi 13.0.3 reads unchanged `1449b.lp` as minimize `a` with `a >= 1`, optimum 1.
The frontend now supports this inline constraint-header convention and records
it. Gurobi rejects `1449a`, `1448`, and `garbage`; those remain refused.

`1451.lp` exposed a separate wrong-answer bug: `end:` was treated as the end
keyword, discarding the constraint and following integrality declaration. Labels
now take precedence. Standalone LHS numbers expose an independent reader
choice: the mathematical-constant extension has minimum 3; Gurobi treats `1`
as a separate nonnegative variable and obtains 2, while HiGHS drops that term
and also obtains 2. The frontend now records `lhs_numbers=constants` (default)
or `lhs_numbers=variables` (Gurobi interpretation). Successful parsing alone
had concealed both the discarded constraint and this reader distinction. Reader/solver receipts and the focused
feasible-set tests record the distinction.
