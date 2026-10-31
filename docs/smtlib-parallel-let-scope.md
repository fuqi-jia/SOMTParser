# Parallel SMT-LIB let binding scope

This change passes R37c verification. SMT-LIB 2.7 section 3.6.1 specifies
[simultaneous substitution for a let group](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf#page=31).
Each right-hand side is evaluated in the outer scope; the body's local names
become visible together. Sequential dependencies require nested let groups.

Both native parser modes previously registered each new binding immediately.
With outer `x=10`, `(let ((x 1) (y x)) (+ x y))` consequently resolved `y` to
the new `x` instead of the outer one. The expected value is 11.

The parser now stages all right-hand sides before publishing the group's
names. Preserved let nodes and inline expansion follow the same rule. Empty
surface groups are rejected, and the internal empty binding-list builder
returns an error node instead of indexing an empty vector.

Native tests cover outer-name reuse, cross-sort shadowing, nested groups,
nested right-hand sides and quantified variables. Evaluation and free-variable
collection are checked in both parser modes.
