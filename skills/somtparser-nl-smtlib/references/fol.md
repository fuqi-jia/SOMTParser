# First-order logic and entailment

Preserve predicate arity, argument order, quantifier scope and implication
direction. Use uninterpreted sorts/functions for open domains. Distinct names do
not imply distinct objects. Do not infer domain closure or a closed world.

An SMT uninterpreted sort is nonempty. If a source permits an empty domain, use
explicit membership and guarded quantifiers, or an exact finite encoding.
Finite quantifiers may be grounded over exactly the supplied set; unrestricted
ones cannot be replaced by guessed finite samples. Preserve
`forall x exists y` versus `exists y forall x`. Fresh constants represent an
outermost positive existential constraint, not arbitrary quantifier movement.

Uniqueness means existence plus identification of every satisfying witness;
respect the source's equality and tuple semantics.

For premises P and conclusion G, check P for consistency, then P and not G,
then P and G. With consistent premises: UNSAT for P and not G establishes
entailment; UNSAT for P and G establishes contradiction; SAT for both means
undetermined. Solver unknown is computational uncertainty, not the dataset's
undetermined label. Inconsistent premises need their own explicit policy.

If context supplies `somt_goal`, equate it to the conclusion instead of asserting
the conclusion as a premise:

```smt2
(declare-sort Person 0)
(declare-const p Person)
(declare-fun kind (Person) Bool)
(declare-fun helpful (Person) Bool)
(assert (forall ((x Person)) (=> (kind x) (helpful x))))
(assert (kind p))
(declare-const somt_goal Bool)
(assert (= somt_goal (helpful p)))
```

The generic bridge checks the formula; the existing FOLIO adapter implements
the three-way classification protocol. Label agreement is a task metric, not
equivalence of all generated premise formulas.
