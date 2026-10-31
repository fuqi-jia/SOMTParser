# Finite integer quantifiers in observable projection

The NL equivalence checker expands an integer quantifier only when conjunctions
in its guard prove a finite interval for every bound variable. It supports a
universal implication and an existential conjunction. Direct integer bounds and
bounds propagated through variable-to-variable order comparisons are necessary
conditions on the guard. Enumerating their Cartesian product therefore includes
every satisfying valuation. Each instantiated guard is retained unless it
simplifies to a Boolean constant. Substitution respects nested binders.

The expansion runs before observable-array projection. Every resulting concrete
read must still be covered by the observation bridges before a whole array root
can be eliminated. Symbolic reads and unbounded quantifiers retain the previous
exact existential projection. Reference models and generated candidates are not
changed, and successful parsing is not counted as semantic equivalence.

Per-formula defaults are 50,000 enumerated tuples, 5,000 retained instances and
2,000,000 estimated/output AST nodes. Budget exhaustion returns the entire
original formula. Diagnostics report expansion counts, skipped quantifiers and
budget exhaustion; any remaining quantifier keeps `skipped_quantifier_context`
true. These are computation limits, not language restrictions.
