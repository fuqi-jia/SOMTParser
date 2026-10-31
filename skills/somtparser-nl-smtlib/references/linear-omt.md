# Numeric constraints and optimization

Keep name, meaning, unit, sort and domain together in a variable map. Check
inequality direction and coefficient-variable association independently.
Aggregate repeated algebraic terms; do not overwrite aliased contributions.

Use exact constants: `(/ 1.0 3.0)` is rational real arithmetic; `div` is integer
division. Cross multiplication by a known positive constant is exact. With an
unknown-sign or possibly zero denominator, preserve sign and definedness cases.

```smt2
; These nonnegative Real domains must come from the actual source.
(declare-const a Real)
(declare-const b Real)
(assert (and (>= a 0) (>= b 0)))
; a is at least one third of b.
(assert (>= (* 3 a) b))
(declare-const cost Real)
(assert (= cost (+ (* 2 a) (* 5 b))))
(minimize cost)
```

Preserve objective constants, units, signs and weights. Rescaling/offsetting an
objective can preserve optimizers but change the decision/cost relation. Define
auxiliary costs by equality, not one-sided bounds that become tight only at the
optimum. Absolute value is `(ite (>= d 0) d (- d))`; finite maxima can use nested
`ite`. Empty sums are zero; an empty maximum needs a source-defined convention.

Keep hard requirements hard. A weighted preference charges the stated complete
preference, not independently weighted pieces unless requested. Check frontend
support for soft groups and objective priorities. The closed-input route refuses
`set-option`; do not silently turn unsupported Pareto/box or multiobjective
semantics into lexicographic/scalar optimization. An exact explicit penalty
expression can implement a supported single-objective preference model.

Preserve single/multiple objective order and verify it in the exported script.
Never add a dummy objective to a satisfiability problem. Distinguish feasible,
optimal, unbounded, unattained infimum, unknown and timeout. A model's objective
value alone proves neither optimality nor equivalence to a reference objective.
