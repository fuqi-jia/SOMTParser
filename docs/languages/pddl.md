# PDDL to SMT: Bounded Planning Construction

This development candidate implements classical/ADL, numeric, derived,
temporal and continuous constructions through shared typed HIR APIs. One domain
and one problem are required. `plan_horizon` bounds deterministic action
occurrences; FOND has separate `fond_policy` and `policy_size` options.
Integrated server qualification of the current candidate is pending.

| Construct family | Implementation |
|---|---|
| STRIPS, typing and ADL | Finite grounding including `(either ...)` parameter types, preconditions, conditional effects and frames |
| General numeric fluents and metrics | Partial real values, strict definedness, simultaneous old-state assignment/additive/scaling updates and final-state objectives |
| Positive derived predicates | Finite least fixed point in each state and at every trajectory point |
| Durative actions | Rational timestamps, state-dependent/empty duration constraints, overlap, history and interference |
| Timed initial literals | All mandatory external events and stable-goal makespan |
| Continuous numeric effects | Coupled trajectories, cumulative rates, complete interval invariants and remembered start guards |
| FOND `oneof` | Bounded strong / strong-cyclic policy graph with explicit options |
| Object-valued functions | Typed finite state, nested terms, dynamic predicate/numeric addresses, simultaneous object assignment and frames in deterministic sequential and temporal traces |
| PDDL 3 trajectory constraints/preferences | Ten finite-trace modalities over classical/temporal observations; quantified goal/action preferences and exact named/anonymous violation metrics |
| Temporal/continuous object and preference combinations | Guarded dynamic-address interference, object pre/post frames and whole-interval state; soft endpoint read access, event-based temporal preferences and an explicit continuous observation policy |
| Continuous over-all/end guards | Not implemented |

See [planning HIR API and validation](../planning-hir-candidate.md) for the
continuous endpoint policy, API composition, tests and remaining qualification.
An available API or successful SMT load alone does not prove correctness.

Numeric effects read the old state. Additive occurrences accumulate, unchanged
cells retain value and definedness, assignment can initialize a cell, and
relative updates require a defined old value. Helper-function bodies take part
in dependency checks so they cannot hide a next-state reference.

A temporal happening is a set of instantaneous ground actions: repeating the
same ground action at one timestamp executes it once. Distinct durative
occurrences retain independent intervals and conditional-effect histories.
Continuous flow connects the discrete post-state to the next pre-state and
exposes its whole trajectory in the source observation map. The horizon bounds
actions, not the number of mandatory timed initial events.

The classical and FOND constructions below retain their original
fragment-specific verification record. Those results do not automatically
qualify the new numeric/temporal implementation.

<!-- implicit-constraints:
  a ground atom omitted from `:init` => false at state 0 under the closed-world assumption; leaving it unconstrained enlarges the initial-state set
  an action effect that does not mention a fluent => that fluent is unchanged; alpha must materialize the frame relation
  simultaneous triggered add and delete effects for one fluent => add takes precedence in PDDL progression
  a typed action or quantified variable => ranges over domain constants and problem objects whose declared type is a subtype of the required type
  a sequential plan step => exactly one source action or one generated suffix-noop; allowing several source actions changes sequential planning into parallel planning
  a plan of length at most k => a source-action prefix followed only by generated noops; forcing k source actions loses dead-end plans shorter than k
  a generated noop => omitted by beta and never reported as a PDDL action
  an unlisted or unknown `:requirements` feature => malformed or unsupported input, not permission to infer semantics from surface syntax
-->

## Source Institution

For an accepted **deterministic** domain/problem pair (the FOND case is below):

\[
\mathcal I_{PDDL}=(\mathbf{Sign},\operatorname{Sen},\operatorname{Mod},
\models,\operatorname{Cost},\preceq,\operatorname{Obs}).
\]

- **Sign** contains the finite type hierarchy, named objects, Boolean fluent
  predicates, and deterministic action schemas.
- **Sen** is the domain/problem pair: initial state, action preconditions and
  effects, and goal.
- **Mod** consists of finite state traces paired with a sequence of applicable
  ground actions.
- **Satisfaction** requires the closed initial state, action progression with
  frame semantics, and a final state satisfying the goal.
- **Cost/order** is satisfaction, or minimization of accumulated `total-cost`.
- **Observables** are the decoded ground actions in plan order.

The unbounded source question is plan existence. With horizon `k`, the target
asks only whether a plan of length at most `k` exists. This is a sound bounded
under-approximation: target SAT yields a real source plan; target UNSAT proves
only absence of plans within the recorded `PLAN_HORIZON`.

## Action costs

The deterministic fragment accepts a nullary `(total-cost)` function, static
numeric functions with typed object arguments, exact nonnegative decimal initial
values, `(increase (total-cost) amount)` effects, and the optional metric
`(:metric minimize (total-cost))`. Every ground numeric function application
must be initialized exactly once. The amount is a nonnegative constant or a
static function application; dynamic numeric guards, assignments, decrements,
arithmetic cost expressions and policy costs are refused. Strict mode requires
`:action-costs`; the existing lenience option records an undeclared requirement.

Each selected action obeys `cost[i+1] = cost[i] + sum(triggered increases)`.
Conditional effects evaluate guards in the old state, universal effects add
each ground increment, and noops preserve cost. Rational literals avoid
floating-point rounding. The final accumulator is the minimization objective.
This preserves costs and their order for admitted plans; a bounded optimum is
not a claim of global optimality. Use the Z3 OMT output dialect when sending
the objective to Z3.

HDDL supplies the set of ground actions appearing in complete bounded
decompositions. The shared encoder validates all source schemas before this
restriction, then instantiates only those actions. Ground tuples changed by no
retained action or compiled method event are evaluated in the closed initial
state. Their implicit false tuples are not Cartesian-grounded: source facts
use injective tuple keys, and unlisted tuples evaluate to false. Every queried
or initial tuple still undergoes declaration, arity and type checks, including
conflicting positive/negative initial facts. Every positive or negative effect
target of a retained action is included, also inside quantified or conditional
effects whose guards happen to be false. Those tuples keep their ordinary
dynamic state encoding. All remaining tuples reconstruct directly from the
closed initial state, including unchanged tuples of otherwise mutable
predicates. This preserves the complete transition relation over retained
actions. Standalone deterministic PDDL uses the same representation after its
bounded action grounding. FOND retains its complete state coordinates.

## Translation Construction

The executable adapter is

\[
\mathcal T_k=(\Phi_k,A_{\Sigma,k},\alpha_k,\beta_k,h).
\]

### Signature map `Phi_k`

Grounding enumerates each predicate and action over all admissible objects,
including inherited subtypes and domain constants. Every bounded state
coordinate `state[i]::(p o...)` and source action choice
`choice[i]::(a o...)` maps injectively to a target Boolean constant. Preferred
readable target names are retained when collision-free; colliding concatenated
names receive an injective suffix. The mapping is recorded in `symbol_map`.

### Encoding axioms `A_Sigma,k`

At each step, one source action or the generated noop is selected. Auxiliary
prefix bits record whether an earlier choice was selected; a later choice is
excluded whenever that prefix is true. Together with the at-least-one clause,
this gives exactly one choice using a linear number of axioms. Prefix bits are
target-only witnesses and add no source observables. Noop preserves every fluent, and

\[
noop_i\Rightarrow noop_{i+1}
\]

makes generated noops a suffix. These administrative relations are stored as
target axioms in the semantic contract.

### Sentence map `alpha_k`

The initial state asserts every listed atom and negates every other ground
atom. Conditions map homomorphically to Boolean operations; object equality is
decided after grounding. Finite `forall` and `exists` become conjunction and
disjunction over the typed object domain. These expansions use flat n-ary
Boolean nodes, so a large finite domain does not create a linear-depth HIR
chain. Parsing transfers the initial fact table between stages instead of
retaining duplicate syntax trees; every literal still receives the same checks.

Standalone deterministic action grounding first computes a conservative
reachability approximation for the requested horizon. Each layer retains all
previous possible facts, ignores deletes and adds every positive effect of
potentially applicable actions, including conditional effects without testing
their guards. Mandatory positive conjuncts join these sparse fact relations;
remaining parameters are streamed over their typed domains. Equality and
three-valued evaluation can reject impossible conditions. A possibly true
mutable atom remains unknown, so negation cannot remove an action enabled by
a later deletion. Quantified conditions remain unknown during this pruning
and receive their ordinary exact expansion in the emitted model.

Inductively, each layer contains every fact that can hold after that many
source actions, so every action in a real bounded plan is retained. Ground
actions excluded this way have no choice coordinate; their reconstructed
selection is false. Dynamic fluent coordinates, original preconditions,
guarded effects and costs remain in the transition encoding. Schema validation runs
before pruning, including unreachable actions and empty object domains.
HDDL uses its hierarchy-derived action set; FOND retains full grounding.

For action `a`, fluent `f`, and old-state effect guards, define

\[
Add_{a,f}=\bigvee\{g\mid (when\ g\ f)\},\qquad
Del_{a,f}=\bigvee\{g\mid (when\ g\ (not\ f))\}.
\]

The successor-state relation aggregates the effects of the selected action:

\[
f_{i+1}\leftrightarrow
\left(\bigvee_a (a_i\land Add_{a,f,i})\right)
\lor\left(f_i\land\neg\bigvee_a(a_i\land Del_{a,f,i})\right).
\]

Because choices are one-hot, this is equivalent to a separate implication
for every action and fluent, including the no-effect noop. Only actual effect
occurrences enter the disjunctions, and each fluent gets one successor equation.
It implements conditional effects, the frame rule, and PDDL's add-over-delete
precedence without constructing the action-by-fluent Cartesian product.
Preconditions are guarded at the state where the action is selected. The goal
is asserted at state `k`.

### Model and objective maps

`beta_k` decodes each one-hot choice to its source action spelling and removes
the generated noop suffix. Therefore a padded target witness projects to a
source plan of length at most `k`, not a fictitious fixed-length plan. There is
no objective in the accepted fragment, so `h` is the identity satisfaction map.

## Correctness Obligations

For the bounded problem `P|k`:

\[
N\models A_{\Sigma,k}\land\alpha_k(P)
\Longrightarrow \beta_k(N)\models P\ \land\ |\beta_k(N)|\le k.
\]

Conversely, every source plan of length at most `k` extends with a unique noop
suffix to a target model. Thus the bounded reduction is exact. Relative to the
unbounded planning question it remains incomplete, which is why the contract
records an under-approximation rather than `Fidelity::exact()`.

## Refusal Policy

The frontend rejects unknown sections and requirements, malformed type or
predicate applications, mismatched domain/problem names, undeclared feature
use, extra problem files, and invalid horizons. FOND `oneof` is not encoded as
an existential branch: its solution is a policy against environment choices,
not a classical action sequence. HDDL tasks/methods are likewise refused
because goal reachability alone would discard decomposition semantics.

## Verification Record

Focused tests cover the closed world, precondition timing, frame/successor
relations, one-hot choice, noop suffix projection, type inheritance, constants,
finite quantifiers, conditional effects, add/delete conflict, explicit feature
requirements, `Phi`, `A_Sigma`, and `beta`.

Z3 returns SAT for the local STRIPS, dead-end-short-plan, and ADL fixtures. On
the vendored deterministic Childsnack problem, horizons 1, 2, and 3 are UNSAT
and horizon 4 is SAT; the model selects make-sandwich, put-on-tray, move-tray,
and serve in order. FOND domains require an explicit policy mode; they are never reinterpreted as
classical favorable-path planning.

Run the focused check with:

```sh
cmake --build build --target test_pddl test_semantic_core
./build/test/test_pddl
./build/test/test_semantic_core
```

## Primary References

- [PDDL 1.2 report record](https://www.isi.edu/results/publications/19837/pddl-the-planning-domain-definition-language-version-1-2/)
- [IPC PDDL resource page](https://ipc08.icaps-conference.org/deterministic/PddlResources.html)
- [Fast Downward PDDL support](https://www.fast-downward.org/23.06/documentation/pddl-support/)
- [VAL reference validator](https://github.com/KCL-Planning/VAL)


## Bounded FOND policy construction (2026-09-23)

Example:

```python
import somtparser as sp

result = sp.translate("languages/pddl/instances/ok/fond-retry.pddl",
                    data=["languages/pddl/instances/ok/fond-retry.problem.pddl"],
                    profile="bmc",
                    options={"fond_policy": "strong-cyclic", "policy_size": "2"})
assert result.exit_code == 0, result.diagnostics
```

`fond_policy=strong` requires reaching a goal under adversarial outcomes.
`strong-cyclic` assumes each outcome of an infinitely repeated state/action
occurs infinitely often. These differ on a retry-or-succeed action: it admits
a fair policy, but no strong policy. See the definitions and fairness
characterization in [Rodriguez et al.](https://arxiv.org/html/2103.08391).

The implementation uses at most `N=policy_size` active nodes, each storing a
complete Boolean source state. Node 0 is active and equals the closed initial
state. Active states are pairwise distinct. Each active nongoal state chooses
one applicable grounded action; inactive and goal nodes choose a terminal
marker. For **every** outcome of that action, an active node must equal the
full successor state, including unchanged fluents and conditional effects.
Independent `oneof` groups form a Cartesian product. Existentially selecting
one favorable outcome is not this construction.

Each node has an auxiliary integer rank in `0..N-1`. In strong mode every
outcome must decrease rank. In strong-cyclic mode every nongoal node must have
at least one rank-decreasing outcome, while **all** outcomes remain covered.
Following decreasing edges gives a goal path from every active node: a
nongoal of minimum rank would violate its progress obligation. Hence there is
no closed nongoal component. Under the explicit outcome-fairness assumption,
an infinite nongoal execution would have a recurrent state whose decreasing
successor must also recur; repeating this argument contradicts the finite
rank range. Strong mode needs no fairness because every execution decreases
rank at every step.

Conversely, a policy whose reachable states number at most `N` embeds in these
nodes. Strong policies use a longest-path rank; strong-cyclic policies use
shortest distance to a goal. Unused nodes are inactive. The restriction is on
policy states, not action executions: strong-cyclic executions may take
arbitrarily many retry steps. The report carries `STRATEGY_SIZE` and a sound
under-approximation; bounded UNSAT is not a global no-policy answer.

The source configuration exposes decisions separately: `PLAN_EXISTENCE`
requires `PLAN_HORIZON`, and `REACTIVE_REALIZABILITY` requires `STRATEGY_SIZE`.
`SourceSemanticSpec.decision_bounds` records these per-decision obligations in
both C++ and Python. This avoids weakening contract validation by accepting a
trace horizon as a policy bound.

The beta projection exposes `policy-active[i]`, each source fluent under
`policy-state[i]::(...)`, and the chosen source action under `policy-action[i]`.
Inactive nodes are ignored; terminal markers and ranks are omitted from action
observables. An independent checker reconstructs reachability from the emitted
model and checks every outcome on the source transition graph.

Current resource limits are 64 policy states, 256 expanded outcomes per action,
and three million fluent/outcome/state-pair construction cells. Exceeding a
limit is a diagnostic, never a truncated model. `oneof` inside a universally
quantified effect remains unsupported because its choices must be independent
for each object. Mixed/conditional fairness, partial observation, numeric
fluents and costs remain outside this fragment.

Validation is recorded in the corpus audit.
The focused tests compare 20 generated four-state graphs in both modes
(40 cases) with exhaustive policy search, replay SAT witnesses, distinguish retry fairness from
strong planning, and reject a good branch hiding an unavoidable dead end.

Action exclusivity uses a linear Boolean prefix encoding. Successor values are
shared across target nodes; unchanged fluents use their current value directly.
Each Boolean state and each computed successor receives an injective bit-vector
signature (one bit per grounded fluent, a constant bit for the empty vocabulary).
Equality compares signatures rather than duplicating every fluent comparison
for every target. The defining equalities fix all auxiliary bits uniquely; beta
still exposes the original Boolean fluents. Balanced concatenation retains odd
trailing bits and avoids a linear-depth term.
A 128-action regression checks distant choices remain mutually exclusive and
the constraint count stays linear. Corpus-scale memory measurements are
required in addition to the small semantic checks.

Additional checks use the vendored source tasks: the Acrobatics SAT policy is
replayed over its actual ground source fluents, including static relations,
and every outcome is checked without consulting target ranks or state
signatures. Beam-walk is UNSAT with seven policy states and SAT with eight,
matching its four locations times the two up/down states forced by falls and
return to the only ladder. These checks distinguish a capacity-bound failure
from absence of an unbounded fair policy.
