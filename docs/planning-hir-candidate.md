# Planning HIR development candidate

This branch implements seven shared planning constructions in C++ and exposes
them through `somtparser.planning`. Server qualification is pending. The
development branch is not a validated release or a complete PDDL coverage result.

| Construction | Implemented relation | PDDL frontend connection |
|---|---|---|
| Numeric state | Exact values with explicit definedness; simultaneous old-state updates, guards, frames and metrics | General numeric functions and arithmetic, comparisons, assignment, increase/decrease and scaling |
| Derived predicates | Finite positive least fixed point; transitive dependencies | Recomputed in every state, with source-syntax reads retained for interference |
| Discrete temporal actions | Ordered happenings, overlapping occurrences, start/end conditions, open intervals, historical guards and endpoint interference | Durative actions with exact rational timestamps and state-dependent durations |
| Timed initial literals | Mandatory external events and earliest permanently achieved goal after the last action | Positive and negative basic literals; stable-goal `total-time` for either metric direction |
| Object state API | Finite nominal/union types, nested lookups, dynamic addresses, undefined policies, simultaneous assignments and frames | Sequential and temporal object-valued functions, nested/dynamic addresses, guarded interference, frames and named-object projection |
| Trajectory/preference API | Ten finite modalities, explicit whole observation domains, named/anonymous violation counts and metrics | Classical and temporal hard trajectories, goal/action preferences, quantifier grounding and exact metric counts; explicit continuous observation policy |
| Continuous trajectories | Closed-interval continuity, differential equations, definedness and invariants at every applicable real time | Continuous effects, overlapping signed rates, causal start guards, complete pre/post states and pointwise derived closure |

The source action bound is explicit: `plan_horizon=k` limits temporal action
occurrences, while all timed initial events are included independently of k.
Repeated action occurrences may overlap. SMT UNSAT only proves absence within
the recorded bound. Rational timestamp witnesses have no fixed denominator or
precision limit. Numeric/predicate namespaces remain distinct even when the
source names coincide.

## Public construction API

Include `somtparser/hir/planning_numeric.h`, `planning_derived.h`,
`planning_temporal.h`, `planning_timed_initial.h`, `planning_continuous.h`,
`planning_objects.h`, or `planning_trajectory.h`.
The C++ builders return explicit typed deltas. Full HIR type checking and the
ordinary translation pipeline validate their composition.

Python clients use `from somtparser import planning`. Numeric and temporal
builders return constraints to attach explicitly. Timed-event placement also
returns matches and endpoint accesses to compose with the state transitions.
The derived convenience binding appends its validated closure delta; clients
equate their observation atoms with the returned closure values. Continuous
encodings provide `to_model(context)`, which returns a validated copy containing
every trajectory declaration and flow constraint.

`examples/planning_continuous_api.py` constructs and exports either a general
trajectory relation or a supplied polynomial witness. The general relation
encodes continuity and differentiation through exact quantifiers. The witness
path verifies the supplied curve and its derivative. A fixed-degree polynomial
search is not a complete search over differential-equation solutions. SMT
solver `unknown` remains unknown; this API does not promise a decision procedure
for arbitrary differential equations.

## Continuous source contract

Each happening has a pre-state and a simultaneous discrete post-state. Between
successive happenings, all active continuous effect occurrences contribute to
the differential equations; an unchanged coordinate has rate zero. Finite
`forall` preserves effect multiplicity, including identical updates from
different bindings. Undefined numeric values propagate through Boolean
expressions. Derived predicates use a finite least fixed point at each time.

Over-all conditions are checked throughout open intervals and on both sides
of internal happenings. The frontend uses `CLOSED_ONE_SIDED`: a defined flow
restricted to each compact interval, with one-sided endpoint derivatives.
The public API also offers `INTERIOR`; callers select the policy explicitly.
These are different source contracts, not interchangeable optimizations.

Conditional continuous effects currently accept remembered at-start guards.
Over-all/end guards on a continuous effect are rejected as noncausal, consistently with [VAL’s causal check](https://github.com/KCL-Planning/VAL/blob/3c7a1f330bdab0ba28a4762bb45c3f06c27fb6d4/libraries/VAL/src/Plan.cpp#L1683); accepting a self-consistent future-dependent trajectory would assign a different semantics. The permissive BNF alone does not establish a causal interpretation.
The relation represents whole real-valued functions, not sampled timestamps.

## Validation and original corpora

The sealed second combined server run exercises the complete public
PDDL→HIR→SMT pipeline for numeric, derived, temporal and timed-event cases. It
includes source contract validation, typed passes, complete target loading,
independent source relations and metric checks. Its corpus driver is
`tools/pddl_translate.cpp` (the `somt-pddl-translate` tool); it emits complete SMT and the native
translation report, with explicit horizon and requirements mode.

Initial server runs passed nine numeric API relation checks and 18,432 temporal
relation cases plus 80 interference cases; their evidence was archived and
hash-verified. These runs preceded later fixes and do not qualify the current
combined candidate.

New continuous source controls contain 34 cases: 25 accepted inputs with exact
fixed-schedule, whole-function witness relations, and nine explicit rejections.
The oracle checks all pre/post values, definedness, derived trajectories and
signed objectives against independent expectations. These controls await
server execution. The numeric helper dependency fix and 20 independent temporal
source regressions are included in the next combined run. Full native, Python, and official-corpus
qualification remain pending. The collected next corpus comprises 400 official
IPC2023 numeric pairs, 90 fixed-revision IPC2018 temporal mirror pairs, and 339
official IPC2004 timed-initial pairs. Collection is not conversion accuracy.
One original numeric problem has a mismatched domain name. Its bytes and raw
result remain preserved, but it is excluded from valid-input conversion rates:
829 collected pairs, 828 candidate-valid pairs pending validation, and one
confirmed invalid source pair. No queued check is reported as passing.

Object and trajectory constructors now have public C++ and Python APIs.
Object construction requires explicit undefined-value and writer-conflict
policies; every returned obligation must be attached to the model.
Trajectory encodings separate domain constraints from satisfaction, so soft
preferences measure violations without rejecting a plan. Their finite modal
semantics follows the final [PDDL3 author paper, Figure 1](https://users.cecs.anu.edu.au/~patrik/publik/ipc5-aij.pdf);
continuous observation domains are explicit separate contracts.

The two new API runs are queued separately: 24 object relations with 20 invalid
construction controls, and 36 trajectory/preference relations. Public Python
checks also cover simultaneous swaps, dynamic target aliasing, nested lookups,
undefined state, guarded object/numeric dependencies, and precondition/update/
exact-cost composition. These are test definitions; server results are pending.

The deterministic sequential frontend now connects both APIs. Object functions
use their declared nominal/union return types; initialization, nested lookup,
dynamic effect addresses and all assignment right-hand sides use the source
state. The recorded policy is `STRICT` undefined propagation and
`SINGLE_WRITER`; omitted object initialization is undefined. Source projection
includes the exact object name or undefined, as well as value/definedness
coordinates. Temporal object interference includes selected dynamic addresses and derived dependencies. Object values remain constant between happenings; the current interval object state selects continuous-effect addresses. These are explicit extensions of the preliminary PDDL3.1 proposal, documented in [the temporal object contract](languages/pddl-object-temporal.md).

Classical PDDL 3 constraints use actual source states, excluding generated
suffix padding. Domain constraints are hard; problem constraints may contain
preferences. Preferences in preconditions are counted for each executed ground
action occurrence. Outer quantified preferences remain separate instances,
while quantification inside one preference contributes one violation. Shared
names sum their instances; empty quantified domains contribute zero. Anonymous
preferences add a unit penalty to minimization and subtract it from maximization.
Time-bounded classical modalities use the sequential step coordinates. Temporal modalities observe the initial state and each actual happening post-state, including every timed initial event independently of goal makespan. Continuous preference observations use an explicit whole-time policy with both sides of internal happenings. Soft endpoint preferences contribute read accesses to no-moving-target checks, even when their satisfaction is not required.

The combined source controls add 62 object examples and 51 classical trajectory/
preference examples, plus four domain-grammar checks and eight combined object/preference/cost relations. Object controls include
three unchanged official PDDL 3.1 example pairs; the Depots example crosses the selected strict nominal application policy and retains its original diagnostic. This does not classify the official example as invalid.
These are focused semantic controls, not a competition coverage percentage.
Server execution of the combined source candidate remains pending.

The next temporal source qualification adds 42 temporal preference inputs, 35 temporal object relations, 18 soft-preference concurrency relations and 18 timed-event endpoint relations. An unchanged classical temporal fixture is upgraded to an accepted case with four full schedule relations. Seven object controls and five preference controls use entire exact continuous witnesses. These counts describe authored checks; all require actual server results.

Thirteen additional composition controls cover object-address selection in soft temporal preferences: selected and unselected dynamic targets, selector changes, undefined values and same-occurrence reads, with full object trajectories and exact violation costs.
