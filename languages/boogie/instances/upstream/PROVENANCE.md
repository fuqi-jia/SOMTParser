# Upstream corpus — Boogie

Unmodified files from **Boogie**, `Test/textbook/`.

- Source: https://github.com/boogie-org/boogie/tree/master/Test/textbook
- Licence: MIT (Boogie contributors)

The first run was **0 of 6**, and the failures were not the ones the coverage
table predicted. They named four constructs the table had never counted:

- `const` and `function`, both refused outright, though both map onto the HIR
  exactly (a `VarDecl` and a `FunDecl`). A function with a body becomes a
  declaration plus `forall x. f(x) = body` rather than being inlined -- both are
  exact, and the axiom form survives a recursive definition, which Boogie allows.
- **Declaration order.** `TuringFactorial.bpl` uses `Factorial(n)` on line 9 and
  declares it on line 31. Boogie does not order declarations; this frontend
  required declare-before-use and rejected a legal program. Now two passes.
- **Quantifiers**, which the file's own axioms are written in, together with
  triggers (`{Factorial(n)}`) and attributes (`{:include_dep}`).
- Grouped names -- `var qq, rr: int`, `procedure T(a,b: int) returns (q,r: int)`,
  `function mode(a, b: int): int` -- which appear in nearly every real file.

DivMod.bpl now translates. The other five refuse for reasons that are design
decisions rather than gaps, and each is refused BY NAME: map types are Boogie's
heap encoding (Bubble, DutchFlag), and `goto`/labels/`if` need the loop-invariant
and branching choices this frontend deliberately does not make (Find,
McCarthy-91, TuringFactorial).

1 of 6 is the honest measure of the distance to real Boogie. No hand-written
fixture would have reported it.

## 2026-08-16 — maps and `old` landed, and the failures converged

Two of the six were refused for map types and two more for `old`. Both are now
supported, and neither is an approximation: a Boogie map and an SMT-LIB array
are both total functions, and `old(x)` is the unversioned name this frontend's
SSA already keeps.

The count is still 1 of 6, and what changed is that **every remaining failure is
the same one**: `while`, `goto`, `if`, a label. That is one decision — how a
loop's invariant is encoded (`docs/languages/boogie.md` §4.3) — rather than the
five separate gaps the coverage table used to list, and the table now names the
decision instead of its symptoms.
