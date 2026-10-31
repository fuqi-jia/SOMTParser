# Upstream corpus: HDDL

These 17 unmodified `.hddl` files come from the BSD-3-Clause
[`pandaPIparser` test directory](https://github.com/panda-planner-dev/pandaPIparser/tree/master/tests),
retrieved 2026-08-17. They form eight domain/problem pairs plus one companion
constants file.

The corpus tests the reference parser's syntax surface; it is not uniformly a
set of requirement-complete planning instances. In particular, several domains
exercise quantified conditions, negative preconditions, or conditional effects
while declaring only `:typing` and the legacy `:hierachie` spelling. The SOMT
frontend keeps PDDL feature declarations semantic: it does not silently infer
missing requirements.

## Current audit

With `plan_horizon=10` and `decomposition_depth=5`:

- `empty-d` / `empty-p` translates; it checks an empty method/frontier.
- `interleaving-d` / `interleaving-p` translates; it checks partially ordered
  method expansions whose valid primitive executions must interleave.
- `conditional-effect`, `conditional-test`, `constant-in-method-test`, and
  `effect-precedence` are refused because their PDDL constructs omit required
  feature declarations.
- `method-effect` writes a method `:effect` and declares
  `(:requirements :typing :hierachie)` — not `:htn-method-pre-eff`, which is the
  requirement the reference grammar gates the construct behind. Refused as a
  missing requirement under the strict default; under `lenient_requirements=1`
  the refusal becomes the semantic one, because `:htn-method-pre-eff` is
  specified only as "similar to the ones used in SHOP" and an analogy is not a
  decomposition rule. See `docs/languages/hddl.md`.
- `minecraft-costs` is the same, for method preconditions, and would not
  translate even with the construct implemented: it also declares
  `(:functions (total-cost) - number)` and writes `(increase (total-cost) ...)`,
  which is numeric planning and outside the accepted Boolean fragment.

The explicit `(:types object)` used by the corpus is normalized as the identity
declaration of the built-in root type. No hierarchy section, method condition,
or binding restriction is erased to obtain these results.
