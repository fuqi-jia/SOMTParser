# VMT-LIB - symbolic transition systems over SMT theories

**Audit date**: 2026-08-25
**Status**: safety translation implemented in `languages/vmt/`; liveness is refused.

<!-- implicit-constraints:
  a variable annotated with :next and the named next variable => one state component with current/next spellings; the next spelling is not an independent input (§1, §3)
  an unpaired nullary variable => an input freshly valued at each transition, not a persistent state variable (§1)
  absent :init or :trans annotations => the empty conjunction true; no implicit initial value or frame equation (§1)
  :trans omits a state update => that next-state component is unconstrained, not equal to its current value (§1, §4)
  :invar-property p => search for a reachable state satisfying not p; the source annotation states the desired invariant rather than the bad state (§1, §3)
  BMC depth k => SAT denotes a real counterexample of length at most k, while UNSAT establishes no unbounded safety result (§3)
-->

VMT-LIB is not plain SMT-LIB with optional comments. Its `!` attributes define a
transition system, so ignoring them preserves SMT syntax but destroys source semantics.
This frontend performs structural annotation extraction before elaborating the contained
terms with the repository's SMT-LIB parser.

## 1. Source semantic configuration

The confirmed format specification is **VMT-LIB 0.1**. A source system is

```text
S = (X, Y, I(X), T(Y, X, X'), {p_i(X)})
```

where `X` is the state signature, `Y` contains inputs, `I` is the initial relation,
`T` is the complete transition relation, and each `p_i` is an invariant property.
A finite path `s_0,...,s_j` satisfies `I(s_0)` and each transition
`exists Y. T(Y,s_r,s_{r+1})`. A property is false exactly when some reachable final
state satisfies `not p_i`.

The assumption profile is inherited from SMT-LIB: functions and arrays are total,
equality is theory equality, arithmetic and quantifiers follow the selected SMT theory,
and VMT attributes are semantic. Important transition assumptions are:

- `(! x :next xn)` makes `x` a state variable and `xn` its next-state spelling;
- every unpaired nullary variable is an input, fresh at each transition;
- `:trans` is the whole relation; omitted state updates are unconstrained, not framed;
- multiple `:init` or `:trans` terms are conjoined;
- an absent `:init` or `:trans` section is the empty conjunction `true`;
- `:invar` is not a VMT-LIB 0.1 annotation and is refused rather than invented.

## 2. Accepted surface and validation

The structural reader accepts `set-logic`, `set-option`, `declare-sort`, `define-sort`,
`declare-fun`, `declare-const`, and `define-fun`, plus a final `(assert true)`.
`define-fun` calls in annotated terms are expanded as source macros. Other declared
functions remain static symbols in the target signature.

The reader handles multiple attributes and nested annotated subterms. It rejects:

- non-variable, undeclared, self, non-injective, or sort-mismatched `:next` pairs;
- input or next-state variables in `:init`;
- input or next-state variables in invariant state properties;
- non-`true` values on `:init`/`:trans` and duplicate or negative property IDs;
- non-VMT commands, non-final `assert`, malformed depth values, and unsupported temporal
  properties.

## 3. Translation contract

For bound `k`, the signature map `Phi` creates `x@0,...,x@k` for every state and input
variable. A next-state name is not an independent target variable. Static sorts and
uninterpreted functions are preserved. The target-side assumptions `A` contain no frame
axioms.

The sentence translation is:

```text
alpha_k(S) = I(X@0) and
             OR over properties i and depths 0 <= j <= k of
               (AND over 0 <= r < j of T(Y@r, X@r, X@(r+1)))
               and not p_i(X@j)
```

Each disjunct is a complete finite path prefix. Transitions through the configured bound
must not be asserted globally: a real counterexample at depth `j` need not be extendible to
depth `k` when `T` has a dead end.

The model projection `beta` removes source `define-fun` wrappers and next-state aliases,
then maps each `x@r`/`y@r` assignment back to the corresponding finite source trace.
There is no optimization map `h` because VMT safety has no objective.

Within the recorded bound the reduction is sound and complete:

```text
target SAT  <=>  a source counterexample exists at some depth <= k
```

Against unbounded safety it is an **under-approximation**: SAT is a real counterexample;
UNSAT means only that no counterexample exists within `k`. The report records
`BMC_DEPTH=k`, and the decision mapping inverts target SAT into source safety failure.

## 4. High-risk semantic differences

### Host-language acceptance

A generic SMT-LIB reader legally drops unknown term attributes. It can therefore accept a
VMT file while losing `:next`, `:init`, `:trans`, and the property query. VMT detection must
use content as well as `.vmt`, and callers must select `--from vmt` for ambiguous input.

### No frame default

| Format | Missing update semantics |
|---|---|
| AIGER | every latch carries its specified next literal |
| BTOR2 | a state without `next` is a primary input, fresh each step |
| PDDL | unaffected fluents persist by action semantics |
| VMT-LIB | exactly what `:trans` states; add nothing |

Adding `x' = x` to VMT changes the reachable set and can hide a counterexample.

### Property polarity and multiplicity

`:invar-property` states what must hold, unlike AIGER/BTOR2 `bad`, which states the
violation. The target must negate VMT properties. The default SMT query aggregates
all invariant properties as "find any violation"; **since 2026-09-19** an optional
`check_index=<n>` (file order, MoXI's selector idiom) restricts the query to one
property, so a harness running the file once per index gets an independent verdict
per property id. The selection is recorded in the translation report's
`EncodingChoice` rationale with the covered id and the note that the remaining
properties are separate queries — a decision in a source comment would not reach
the experiment's record.

### Liveness

`:live-property` means `FG p`; `:ltl-property` and `:ltlf-property` require temporal
elaboration. A finite safety unrolling cannot represent their counterexamples. The frontend
currently refuses the complete file when any such property occurs rather than silently
treating it as safety.

## 5. Verification evidence

`test/languages/test_vmt.cpp` covers state/input classification, next-pair validation,
macro expansion, nested and multi-attribute terms, property polarity, command validation,
empty-section defaults, malformed bounds, and liveness refusal. The `dead_end.vmt`
regression has an initial counterexample that cannot extend to depth 2; the generated
depth-2 SMT query is `sat` in Z3, confirming prefix semantics.

## 6. References

1. VMT-LIB Format Specification, Version 0.1:
   <https://es-static.fbk.eu/people/griggio/papers/vmtlib.pdf>
2. VMT-LIB project and benchmark/tool links: <https://vmt-lib.fbk.eu/>
3. FBK `vmt-tools` 0.4 reference reader:
   <https://es-static.fbk.eu/people/griggio/ic3ia/>
4. PyVMT reader and model validation: <https://github.com/pyvmt/pyvmt>
5. SMT-LIB 2.6 reference: <https://smt-lib.org/language.shtml>
