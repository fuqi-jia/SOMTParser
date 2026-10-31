# Sequential object-valued PDDL functions

<!-- implicit-constraints:
  a missing initial object-valued function assignment => its cell is undefined, with canonical code zero rather than an arbitrary named object
  a defined object-valued cell => its code belongs to the declared nominal finite carrier
  an action that does not update an object cell => both its value and definedness are framed unchanged
  simultaneous object effect guards, addresses and right-hand sides => all are evaluated in the old state under the declared STRICT policy
  two firing assignments to one object cell => the SINGLE_WRITER policy forbids the happening, even when proposed values agree
  a false defined conditional guard => its inactive address and right-hand side need not be defined
-->

The frontend translates finite object-valued functions into the shared
`planning_objects` HIR API. Return types may be primitive object types or finite
`(either ...)` unions. Nested terms can address other object functions,
predicates, numeric functions and assignment destinations. Function and predicate
names have separate source contexts. Complete nominal type and free-variable
checks run before grounding, including unreachable actions and empty carriers.

This frontend explicitly records the policy
`finite-sequential-strict-undefined-single-writer`. Its semantics are:

- Missing initial values are undefined. A defined value belongs to its declared
  nominal carrier. Initial assignments require ground basic function terms.
- Every selected action evaluates all guards, addresses and right-hand sides in
  the old state. Conditional and universally quantified effects are simultaneous.
  Unchanged cells retain both their value and their definedness.
- Undefined values propagate through object atoms and Boolean connectives using
  STRICT definedness, as for the numeric frontend. Undefined evaluated addresses
  and right-hand sides make a firing effect inapplicable. A false, defined guard
  does not require its effect's address or right-hand side to be defined.
- `assign ... undefined` explicitly resets a cell. `undefined` is not an object
  term and cannot be compared in a condition. Two simultaneous assignments to the
  same object cell are forbidden by SINGLE_WRITER, including equal assignments.
- Basic predicate updates and numeric updates retain their existing policies.
  Derived predicates are recomputed as the finite least fixed point in each
  complete state. Object addresses participate in source dependency metadata.

The complete source signature exposes each grounded function at every trace
state through an integer code and a definedness Boolean. The model projection
also decodes a named object or `undefined` through a one-hot choice. Codes use the
source object's declaration order; zero is the canonical undefined code and is
never an object. These coordinates are observations of source state, rather than
unconstrained uninterpreted functions.

The IPC2008 [PDDL3.1 extension](https://ipc08.icaps-conference.org/deterministic/PddlExtension.html)
is explicitly preliminary, particularly about temporal and unknown-value
semantics. The policy above is an explicit sequential institution; it does not
claim that the preliminary document fixes every undefined/conflict rule.
Temporal and continuous object-fluent domains now compose through the [temporal object policy](pddl-object-temporal.md), including address, right-hand-side and guard interference. Nondeterministic object/numeric/temporal combinations remain outside the bounded Boolean FOND construction.

The isolated source controls compare complete bounded source relations with an
independent Python interpreter using object names, `None`, and exact fractions.
Both public and internal exports are checked by actual XOR satisfiability; every
feasible trace's signed objective is also compared. Original IPC2008 Blocks,
Logistics and Depots examples are retained unchanged. The Depots example passes
`thing-below : (either surface truck)` to `clear : surface`; strict nominal
checking rejects that application under the selected nominal policy. The preliminary proposal does not settle dynamic narrowing, so this is not evidence that the official example is invalid. These files are examples, not a claim of
competition-corpus coverage. Successful whole-target parsing does not establish
that a planning problem is satisfiable.
