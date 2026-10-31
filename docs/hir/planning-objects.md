# Finite object state relations

`somtparser/hir/planning_objects.h` constructs finite object-valued state
relations in ordinary typed HIR. This API is independent of the PDDL parser.
Its presence does not mean that a PDDL file declaring `:object-fluents` is
accepted. The accompanying frontend change supports finite `(either ...)`
parameter domains; complete object-fluent frontend wiring remains separate.

An `ObjectUniverse` lists primitive nominal types and problem objects. The
implicit type root is `object`; explicit type parents form a checked DAG.
An `ObjectType` is a nonempty list of primitive type alternatives. Its carrier
is the union of their finite object domains, with each object appearing once.
A subtype test is nominal: every actual alternative must inherit an expected
alternative. Empty carriers never make unrelated nominal types compatible.
The PDDL union parser normalizes repetitions and order. Concrete objects and
primitive type declarations still require a single nominal type.

Object `i` is represented by the integer `i+1`. An object state cell has an Int
value and a Bool definedness field. Undefined cells have the canonical value
zero, which is not an object. A defined value must lie in the cell's declared
finite carrier. `initialObjectState` makes omitted cells undefined and checks
all explicit initialization types. `undefined` is not accepted by
`objectConstant`: resetting a cell is an explicit `nullopt` RHS in an update.
An undefined evaluated RHS is an execution error when its update fires; it
never silently resets a destination.

`objectDispatch` checks the entire table: its rows must be exactly the Cartesian
product of the parameter carriers, without duplicates. It validates every
argument and row even in an inactive branch or empty domain. `objectLookup`
selects a row value using the current argument values and composes naturally
for nested function applications. It does not introduce unconstrained lookup
functions. `objectPredicate` and `objectNumericLookup` use the same argument
selection to access Boolean and numeric tables. A numeric result carries
separate numeric and object read metadata; their indices name different state
spaces.

Every result's `constraints` must be appended to the consuming model. The
expression and its definedness alone are insufficient: those obligations
establish finite domains and canonical undefined payloads. Build and initial
state operations include their required obligations. The completed HIR model
must pass the ordinary type checker and translation pipeline. Public structs
permit custom expressions, but custom read guards are the caller's contract;
only factory-produced guards are computed by this module. No temporal
interference theorem is claimed for arbitrary user-supplied metadata.

Undefined atoms have two explicit mathematical policies, without a default:

- `STRICT` retains undefinedness through Boolean NOT, OR and implication.
  `objectSatisfied` requires both definedness and truth.
- `ATOMIC_FALSE` makes an undefined atomic equality or predicate false before
  Boolean connectives are applied. Its negation can therefore be true.

These policies deliberately differ. The IPC2008 object-fluent proposal says
that unknown values and temporal semantics need further work. Selecting a
policy in an application must be recorded in its source contract; it is not an
implicit claim about a settled PDDL3.1 temporal standard.

`objectAddress` selects a grounded destination from current object arguments.
`buildObjectTransition` evaluates all guards, addresses and RHS terms in the
old state, applies enabled assignments simultaneously, and frames all other
cells. A reachable `define-fun` body cannot hide a successor-state read.
Read-index metadata is checked against old-state dependencies, including
reachable helper bodies. Dynamic destination aliasing is handled after row
selection. `SINGLE_WRITER` forbids two active writes to one cell;
`AGREEING_WRITERS` permits them only when both resulting value and definedness
agree. Neither policy silently imposes PDDL no-moving-target rules. A temporal
consumer must separately combine guarded object address/RHS reads, guard
reads, predicate reads and numeric reads with its chosen happening semantics.

The source-observation map must retain the universe's ordered object names,
each grounded function tuple, and every state cell's value and definedness.
Code zero decodes to undefined; codes `1..N` decode to those names. Auxiliary
row selectors introduce no additional source observations. During a continuous
interval object cells remain discrete; changing numeric trajectories do not
permit object codes to interpolate.

The independent API controls enumerate every finite old state and guard
combination in their small universes, interpret assignments using Python
objects/`None`, and ask a solver for the XOR of the entire reference and emitted
relation. Separate controls cover bad types, incomplete tables, free variables
and hidden successor-state reads. These controls are not a qualification of
unimplemented PDDL object-fluent syntax or temporal object semantics.

Primary sources:

- [IPC2008 object-fluent proposal](https://ipc08.icaps-conference.org/deterministic/PddlExtension.html): syntax, initialization, explicit undefined assignment, and its preliminary-semantics notice.
- [Kovacs, complete PDDL3.1 BNF](https://helios.hud.ac.uk/scommv/IPC-14/repository/kovacs-pddl-3.1-2011.pdf): nested object terms and object/numeric function arguments.
- [Official examples](https://ipc08.icaps-conference.org/deterministic/PddlExtension.html): examples, not a competition corpus. Some Functional STRIPS files explicitly document type-incorrect source expressions; diagnostics must preserve those original bytes.
