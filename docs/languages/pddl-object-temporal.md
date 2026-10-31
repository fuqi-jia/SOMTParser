# Temporal object-valued functions

<!-- implicit-constraints:
  an object fluent between consecutive happenings => its value and definedness remain constant until an endpoint update
  an endpoint effect => its guard, selected address and right-hand side read the pre-happening object state
  a cell not written at a happening => its value and definedness are framed into the post-happening state
  simultaneous writes to one object cell => the declared SINGLE_WRITER temporal policy rejects the conflict
  an active dynamic object address => its address must be defined and its selected reads participate in no-moving-target checks
  a continuous destination dependent on an object cell => each interval uses the current object state, including any preceding internal discrete update
-->

The frontend records the `finite-temporal-strict-undefined-single-writer`
object policy in its translation report. It extends the same finite, nominally
typed object cells used for sequential PDDL3.1 inputs to the happening grid.
Object values and definedness are separately observable, and named choices
project the finite encoding back to source object names or `undefined`.

This is an explicit temporal extension of the preliminary
[IPC2008 PDDL3.1 proposal](https://ipc08.icaps-conference.org/deterministic/PddlExtension.html),
which did not supply a complete temporal or undefined-value semantics. It does
not claim that the proposal uniquely prescribes every policy below. In
particular, the retained original Depots example exceeds the chosen STRICT
nominal application policy when its union-valued result is passed to a narrower
parameter. The original bytes and diagnostic remain evidence of that policy
boundary, not a claim that an official example was proved invalid.

All endpoint guards, object addresses and right-hand sides use the state before
the happening. Active addresses and values must be defined; a false, defined
conditional guard leaves its unused address and right-hand side unconstrained
by definedness obligations. A selected conditional guard itself remains subject
to STRICT definedness. Updates happen simultaneously, with a frame for every
unmodified cell. Object assignment permits one writer per cell per happening,
even if two writes propose the same value. Explicit assignment of `undefined`
is supported. Object values remain constant between happenings.

No-moving-target checks include reads used to choose an address, evaluate a
right-hand side, test a hard condition, or test a soft condition supplied by the
PDDL3 preference frontend. Dynamic predicate and numeric applications read only
the selected ground row, guarded by the old object value. Their address-object
reads are included separately. Derived conditions traverse the finite, selected
ground dependency graph to all basic, numeric and object reads; cycle removal
uses exact finite reachability, without an arbitrary recursion depth. These
checks extend the happening rules of
[Fox and Long](https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume20/fox03a-html/node12.html).

For continuous numeric effects, destinations and rates use the current object
state in each interval. An internal discrete object update can therefore change
the destination of later flow. Active destinations must be defined, and the
existing continuous API enforces the full interval relation and invariants.
Object trajectories expose both code and definedness functions, with canonical
values outside their interval. Derived predicates are recomputed pointwise,
including object-dependent numeric applications. This implements an explicit
current-state address policy; it does not freeze addresses at action start.
The existing closed-one-sided derivative policy and rejection of
noncausal future/interval-guarded continuous effects remain in force.

The frontend still rejects object/numeric/derived/temporal combinations with
FOND policy semantics. Capability metadata names this remaining combination
rather than listing all object-valued functions as absent. Its historical
feature-family count is not a benchmark success rate.

## Qualification controls

`test_pddl_temporal_objects.cpp` exports public-pipeline and internal targets
for 35 source controls. `check_pddl_temporal_object_relations.py` compares every
exported scalar, named-object choice and signed makespan at each stated rational
schedule. Positive controls require a model and prove that no other observable
tuple is possible; negative controls require UNSAT. Continuous controls supply
entire exact polynomial witnesses, substitute them into the emitted derivative
relation, and additionally compare every exported object/derived trajectory
pointwise. They neither sample times nor decide arbitrary ODEs. Unknown is a
failure. These source controls are authored independently of the implementation;
the stage contract separately records whether they have actually run.

The old `bad_temporal` fixture is retained byte-for-byte and upgraded to an
accepted zero-horizon complete-relation control. Its previous sealed rejection
and sequential evidence are not rewritten.
