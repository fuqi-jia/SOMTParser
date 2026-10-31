# Parallel SMT-LIB let binding scope

This change passes R37c verification. SMT-LIB 2.7 section 3.6.1 specifies
[simultaneous substitution for a let group](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf#page=31).
Each right-hand side is evaluated in the outer scope; the body's local names
become visible together. Sequential dependencies require nested let groups.

Both native parser modes previously registered each new binding immediately.
With outer `x=10`, `(let ((x 1) (y x)) (+ x y))` consequently resolved `y` to
the new `x` instead of the outer one. The expected value is 11. HIR lifting
follows the resolved DAG references, so the frozen R35c diagnostic confirmed a semantic defect,
not merely a spelling difference in exported SMT.

The parser now stages all right-hand sides before publishing the group's
names. Preserved let nodes and inline expansion follow the same rule. Empty
surface groups are rejected, and the internal empty binding-list builder
returns an error node instead of indexing an empty vector.

The checks compare direct source and translated formulas in Z3 and
cvc5, separately asserting each expected relation and its negation. They
include outer-name reuse, cross-sort shadowing, nested groups, nested RHSs and
quantified variables. Native evaluation and free-variable collection are
checked in both parser modes. This change does not yet add a first-class HIR
LET node or preserve textual sharing through HIR lowering.

Before this repair, the frozen-runtime probe found four source/translation
SAT/UNSAT inversions in each polarity with agreement from both Z3 and cvc5;
the cross-sort shadowing pair was refused. Native evaluation returned 2 instead
of 11 in both modes. Raw inputs, outputs and solver versions are retained in
`somt-let-mzn-probe-20260929` on the experiment host.
