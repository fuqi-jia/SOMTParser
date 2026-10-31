# Correctness of bounded planning grounding reductions

This note describes the implemented finite, typed, deterministic Boolean
planning fragment, including old-state conditional effects, finite quantified
effects and the supported action-cost fragment. It does not claim support for
unrestricted numeric or temporal planning. All declarations, schemas, initial
literals and the goal are validated before reductions are applied.

Let `O` be the finite typed object universe, `S0` the closed initial set of true
ground atoms, and `k` the requested plan horizon. A source execution uses at
most `k` applicable actions. Noops in the target pad the end of such an execution.

## Conservative action candidates

Define `F0 = S0`. At layer `i`, the implementation enumerates a set `Gi` of
ground actions that may be applicable in a state contained in `Fi`. Then

```text
Fi+1 = Fi union {every positive effect target of every action in Gi}.
```

All conditional guards are ignored when collecting these positive targets;
finite effect quantifiers are fully instantiated. Deletes do not remove facts
from `Fi`. The union `G = G0 union ... union G(k-1)` is the retained action set.
If a layer adds no facts, repeating it cannot produce new candidates and the
iteration can stop. Reusing an already retained action need not recollect its
effect targets: those targets were already added at its first discovery.

The partial precondition evaluator has three values: false, true and unknown.
For a fully bound atom:

- absence from `Fi` gives false;
- presence gives true only if no source action schema can modify its predicate;
- presence in a mutable predicate gives unknown.

Negation, conjunction, disjunction and implication use their conservative
three-valued operations. Object equality is evaluated only after both terms
are bound. Unbound terms and quantified conditions yield unknown. Thus a
mutable atom's possible truth never proves its negative precondition false;
actions enabled by later deletes are retained. Quantified conditions are
expanded exactly when the actual transition relation is built.

Mandatory positive conjuncts are joined against the relations in `Fi` before
remaining parameters are enumerated over their finite typed domains. Joins
respect constants, repeated variables and declared argument types. The
collector does not descend through negation, disjunction, implication or
quantifier binders when identifying mandatory conjuncts. Every applicable
ground substitution satisfies these joins. No candidate is removed merely
because a dynamic precondition is false in `S0` but can become true later.

The implementation indexes each relation by the argument positions already
bound to constants or earlier variables, and chooses the remaining conjunct
with the fewest matching rows. Reordering conjunction does not change its
solutions; full tuple unification still checks repeated variables and types.
Indexes are local to one immutable `Fi` layer and rebuilt for `Fi+1`, so an
old index cannot hide newly reachable tuples. This avoids large Cartesian
intermediates between otherwise independent parameter groups.

**Invariant.** Every source state reachable in at most `i` actions is contained
in `Fi`, and every action applicable after exactly `i` actions belongs to `Gi`.

For `i = 0`, the state inclusion holds by construction. Assuming it at `i`,
the evaluator cannot return false on a precondition true in an actual state,
and every mandatory positive conjunct matches a fact in `Fi`. Enumeration
therefore retains each applicable action. Its actual positive effects are a
subset of the collected unguarded targets. Retaining old facts while ignoring
deletes includes its complete successor state in `Fi+1`. This proves the
invariant by induction. Pruning actions outside `G` cannot remove a source
execution of length at most `k`.

The first layer retaining a ground action is also a lower bound on its actual
execution index. The encoder now declares that action's choice coordinate and
emits its preconditions/effects only at that layer and later. Earlier omitted
choices reconstruct as false. The invariant above proves that no applicable
source action is lost at any step. In particular, this is not an exact earliest
time: relaxed candidates may appear too early, and their original conditions
still prohibit premature execution. Hierarchy-supplied actions and FOND policy
actions keep their existing unpruned indices.

## Mutable tuple footprint

After retaining actions, let `W` be the union of all their positive **and
negative** ground effect targets, including targets under false conditional
guards and every finite quantified instance. The deterministic encoder
allocates state coordinates only for atoms in `W`.

Every atom outside `W` is unchanged by every retained action and hence has its
initial truth value at every step. Its condition/goal occurrences can be
replaced by that Boolean constant. The original initial table is checked even
for tuples never queried by an action or goal. Source names, arities, typing,
closed-world falsity and contradictory initial facts are still checked.
If actual effect encoding ever encounters a target missing from `W`, it emits
an internal error instead of silently ignoring the update.

This reasoning is per ground tuple, not per predicate. One tuple of a predicate
can change while another remains a fixed true or fixed false fact. Enumerating
the complete Cartesian domain of that predicate is unnecessary.

## Relation between source and target models

Given a source execution of length at most `k`, choose its retained action
coordinates, append target noops, and copy its states restricted to `W`.
Assign the administrative action-selection witnesses accordingly. Every
original precondition, guarded update, frame condition and goal then holds.

Conversely, decode an accepted target's action choices, remove its noop suffix,
and extend each represented state with the initial values of atoms outside
`W`. The untouched atoms satisfy their source frame conditions. The represented
atoms satisfy the original exact successor equations, so each selected action
is applicable and each extended successor is the corresponding source state.
The source goal holds. An omitted action coordinate reconstructs as false;
an omitted fluent coordinate reconstructs as its initial value.

This gives the same bounded source executions and observations, up to target
auxiliary witnesses. Original guarded cost increments and the final objective
are unchanged, so costs and their order are preserved over those executions.
The reduction adds no bound beyond `k`; it does not turn bounded UNSAT or a
bounded optimum into an unbounded claim.

HDDL supplies `G` from complete decompositions within its independently
recorded bounds, instead of the classical reachability construction. The same
tuple-footprint argument applies to primitive actions and compiled method
events. Its separate hierarchy formula still enforces decomposition and
ordering. FOND currently retains its complete state representation and does
not use these deterministic reductions.

## HDDL method candidates and shared scheduling

Let `Add` contain every predicate named by a positive primitive or method
effect, including effects beneath conditional guards and finite quantifiers.
For a Boolean predicate `R` outside `Add`, every reachable state satisfies
`S(R) subseteq S0(R)`: initially this is equality, and a transition can only
retain or delete its tuples. This uses the accepted deterministic fragment;
derived or externally changing predicates are outside this argument.

If a method has a mandatory positive conjunct `R(t)`, a ground substitution
executing that method must therefore satisfy `t in S0(R)`. The same applies
to a mandatory conjunct of any direct primitive child: the child must execute
in every decomposition using that method. Substitute the child's formal
parameters with the method's task-call arguments before applying the join.
Constants, repeated arguments and parameter types remain restrictions on
that substitution. Negation, disjunction, implication and quantified
conditions contribute no joins through their nested atoms.

These restrictions are necessary, not sufficient. In particular, an initially
present tuple can be deleted before the method event or primitive child
executes. Both retain their complete original execution-time conditions.
Any positive effect on `R`, even a guarded or unreachable one, disables this
initial-relation restriction. Thus every actual bounded decomposition remains
in the candidate set, while some impossible candidates can still remain.

For scheduling, let candidate frontier `i` have `n_i` primitive/event
occurrences and let execution capacity `E` be at least every `n_i`. A shared
position vector has `m <= E` entries, where `m` is the maximum unordered
frontier length. All entries lie in `[0,E)` and are distinct. An unordered
frontier `i`'s placement clauses require its first `n_i` positions to be a
permutation of `[0,n_i)` and to satisfy its precedence edges. Every such permutation extends
to the unused `m - n_i` entries, because at least that many unused values
remain. A fixed-sequence alternative requires no positions and can always
extend with an arbitrary injection. Therefore sharing the existential vector
across the disjunction of alternatives neither removes valid schedules nor
admits invalid schedules. Repeated labels still have separate positions.

The factored frontier formula obeys the trie invariant: a terminal node
denotes true, and another node denotes the disjunction over outgoing edges
of `edge_conjunct AND child_formula`. Its root is exactly the original
disjunction of complete path conjunctions. Interning identical suffixes
preserves that invariant; it does not combine arbitrary prefixes and suffixes
from different source paths. This is a Boolean equivalence over the same
global position and action coordinates, with no new semantic bound.

These reductions may reduce the derived execution capacity by discarding
impossible frontiers. Every executable bounded frontier is still present, so
its length still fits that capacity. Resource guards remain possible outcomes
on other inputs; exceeding a guard is not interpreted as source UNSAT.

## Executable checks and limits of evidence

The independent Python source executor in
[`test_pddl_reachable_grounding.py`](../test/python/test_pddl_reachable_grounding.py)
checks all 620 parameterized action/noop traces at horizons 1–3 under four
initial states. It checks every intermediate/final fluent, reconstructing
omitted tuples from `S0`; omitting an actually changing tuple therefore causes
a failure. Additional checks exercise large sparse joins, future enabled
actions, quantifier shadowing and conditional effects. Sparse fluent cases in
[`test_pddl_sparse_static.py`](../test/python/test_pddl_sparse_static.py) include
both kinds of effects and a mutable relation with 512^4 possible tuples.

[`test_hddl_sparse_methods.py`](../test/python/test_hddl_sparse_methods.py)
checks the method/child joins, including changes before execution and formal
to actual argument substitution. [`test_hddl_symbolic_order.py`](../test/python/test_hddl_symbolic_order.py)
compares every short trace against independently enumerated partial orders,
including correlated alternatives, empty frontiers and repeated labels.

These finite checks support the implementation argument; they are not a
mechanically checked proof or semantic validation of every competition task.
Official SMT emission and independent parsing are measured separately in the
planning experiment report.
