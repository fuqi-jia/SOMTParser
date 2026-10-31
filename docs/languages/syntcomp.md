# SYNTCOMP / TLSF 1.2

**Implementation:** `languages/syntcomp/src/syntcomp.cpp`

**Status:** exact decision translation for Boolean stateless invariant games and
basic finite TLSF LTL/LTLf games, and infinite one-step safety contracts with
matching Mealy/Moore semantics and target. The frontend does not yet support
general infinite-word temporal synthesis, TLSF's
extended `GLOBAL` language, parameterized/function/bus declarations, AIGER, or
HOA games.

<!-- implicit-constraints:
  TLSF finite words are nonempty => the initial automaton state rejects epsilon
  Mealy/Moore move order => only Mealy strategy arrays are indexed by current inputs
  standard section semantics => emit initially -> (preset AND ((G require AND assume) -> (G assert AND guarantee)))
  whole-trace assumptions and guarantees => preserve both in the same finite-word formula
  finite reactive realizability => existential controller choices must decrease ranks for every environment move until acceptance
  standard infinite safety implication => a later assumption failure can rescue an earlier guarantee failure
  infinite accepting states => always continue play, never terminate
  temporal strategy witnesses => report the decision reduction without claiming a decoded controller from beta
-->

## Source Semantics

TLSF realizability asks whether a causal controller can satisfy the formula for
every environment behavior. Under TLSF's finite semantics, a controller may
terminate after a nonempty finite word reaches a satisfying automaton state.
The source formula is interpreted over that same finite word; termination is
not approximated by selecting a fixed trace horizon. The definitions are in the
[TLSF 1.2 paper](https://arxiv.org/html/2303.03839v3), especially §§2.1–2.2 and
§3.2.3 (which applies the standard section formula under LTLf semantics).

For `INITIALLY = θe`, `PRESET = θs`, `REQUIRE = ψe`, `ASSERT = ψs`,
`ASSUME = φe`, and `GUARANTEE = φs`, absent sections mean true and the standard
specification (under the selected finite or infinite word semantics) is:

```text
θe -> (θs AND ((G ψe AND φe) -> (G ψs AND φs)))
```

This keeps `PRESET` independent of other environment assumptions, as required
by the paper. `SEMANTICS` and `TARGET` must name the same `Mealy` or `Moore`
model. Strict semantics and cross-target causal transformations are refused.

## Accepted Fragment

The finite temporal-game path accepts basic TLSF Boolean signal declarations and
Boolean expressions with `!`, `&&`, `||`, `->`, `<->`, `X`, `X[!]`, `G`, `F`,
`U`, `R`, and `W`. It handles `INITIALLY`, `PRESET`, `REQUIRE`, `ASSERT`/`INVARIANTS`,
`ASSUME`/`ASSUMPTIONS`, and `GUARANTEE`/`GUARANTEES`. Basic `INFO` metadata,
including comma-separated string `TAGS`, is parsed. It does not claim support
for full TLSF v1.2's optional `GLOBAL` definitions, buses, enumerations, sets,
functions, big operators, or syntactic sugar.

The infinite path accepts propositional `INITIALLY` and `PRESET` sections.
`REQUIRE`, `ASSERT`, and its legacy alias `INVARIANTS` accept Boolean combinations
of current signals and `X` applied to propositional formulas. `ASSUME` and
`GUARANTEE` accept conjunctions of `G` applied to these one-step bodies. Empty
sections mean true. Output-dependent assumptions are included. Nested `X`,
`X[!]`, `F`, `U`, `R`, and `W` remain unsupported under infinite semantics.

The existing truth-table path remains for stateless invariant games with
input-only assumptions and at most 16 inputs. Larger input alphabets and
output-dependent assumptions use the symbolic automaton path; 16 is an encoding
choice threshold, not an accepted-language cutoff.

## Exact Infinite Safety Contract Construction

For the admitted fragment, both sides of the whole-trace implication are safety
properties. A complete deterministic symbolic monitor tracks their formula
derivatives. An environment violation permanently wins. A system violation
remains rejecting until an environment violation occurs; it does not immediately
lose. The first letter separately checks `INITIALLY -> PRESET`. A failed
`PRESET` under true `INITIALLY` permanently loses even if other assumptions fail.
This implements the standard section formula from §3.2.1 of the TLSF paper;
strict implication would have different behavior and remains refused.

The monitor has a Büchi condition: every infinite play must visit accepting
states infinitely often. Acceptance means that the system has not failed, or
the environment has failed. Every state, including an accepting state, must
have a winning successor for every input under the chosen causal outputs.
Rejecting states additionally require a strictly decreasing nonnegative rank.
Accepting states can reset that rank, but cannot terminate play.

For the complete reachable monitor with `N` states, ranks below `N` suffice.
Finite Büchi games have positional winning strategies; after fixing such a
strategy, a reachable cycle containing only rejecting states is impossible.
The longest rejecting path supplies the required ranks. Conversely, rank
decrease rules out an infinite rejecting suffix. See the primary treatment of
[positional games by Grädel and Walukiewicz](https://arxiv.org/abs/cs/0610035).
The encoding is therefore exact for the admitted fragment without choosing a
play horizon or a source-controller memory bound. All reachable states are
constructed; resource exhaustion reports an error instead of truncation.

Mealy output arrays are indexed by the entire current input tuple. Moore output
choices depend on the current monitor state, which contains past information,
and are independent of current inputs. The temporal target is a realizability
decision certificate; the frontend does not claim a decoded controller through
`beta`.

## Exact Finite Game Construction

Formula derivatives form a reachable DFA over nonempty words. Each transition
has a Boolean letter condition represented by a reduced ordered BDD, so the
implementation never enumerates all `2^AP` valuations to construct its
alphabet. Residual Boolean formulas are canonicalized as BDDs over the finite
source-formula closure; temporal recurrence reuses source subformulas. Hence
there are finitely many canonical derivative states, although their number may
be exponential. Resource exhaustion is reported instead of substituting a
chosen horizon or truncating the state space.

Each DFA state has a winning variable and a rank in `[0, N)`, where `N` is the
number of reachable states. Accepting states can terminate. Every winning
nonaccepting state must choose a transition to a winning state with smaller
rank for every current input. A finite reachability game has a positional
winning strategy exactly on its least attractor, and the attractor stage gives
such a strictly decreasing rank below `N`; the rank constraints therefore
preserve both winning and losing decisions without a play bound. Mealy strategy
arrays are indexed by the current Boolean inputs; Moore output choices are
state-indexed constants independent of the current input.

The temporal target contains existential strategy arrays and rank/state
witnesses. It exactly answers the source realizability decision, but the
current temporal encoding does not claim a decoded controller through `beta`.
The stateless response-table encoding retains its existing named controller
projection. No objective or numeric value mapping is involved.

### Exact finite fast paths

The frontend first checks whether the complete finite specification has a
causal winning move on its first position. It quantifies current outputs and
inputs in the selected Moore or Mealy order. A successful check is an exact
one-position finite trace, so the frontend can emit a satisfiable decision
model without constructing the progression DFA. A failed check is not a
negative result; translation continues through the complete automaton and
reachability game.

For an unrestricted environment (no `INITIALLY`, `REQUIRE`, or
`ASSUMPTIONS`), the frontend can also prove some specifications unrealizable
before progression. If the combined guarantees propositionally entail
`G(input)` for an environment signal, the environment can choose that signal
false at the first position and defeat every controller. This reduction keeps
the standard section formula intact and does not treat system-side `PRESET` or
`ASSERT` as environment assumptions.

In the general reachability encoding, the alternatives for a state’s legal
successor moves are represented as one n-ary disjunction. This preserves the
same game relation while avoiding a deeply nested expression tree when a state
has many outgoing transitions.

## Validation

`test/languages/test_syntcomp_finite_automaton.cpp` compares the symbolic automaton against direct
finite-word semantics for 4,680 words over a three-proposition formula and
2,920 words over five nested `G/F/U/R/W` cases; it also tests Boolean-quotient
identities. The actual official `syft_2_068.tlsf` guarantee parses in C++ and
builds a 110-state symbolic DFA. An independent Python explicit-game oracle
checks this instance and finds it unrealizable; its least-attractor result
agrees. Separate examples distinguish Mealy from Moore (`G(i <-> o)`) and
check terminating `F o` games. Public Python end-to-end tests are in
`test/python/test_syntcomp_finite.py`. Official-cohort coverage is reported
separately from these focused checks.

`test/languages/test_syntcomp_infinite_safety_monitor.cpp` compares the monitor
with direct semantics on 2,100 ultimately periodic words and checks complete,
disjoint transition partitions. `test/python/test_syntcomp_infinite_safety.py`
compares exported decisions with an independent explicit Büchi fixed-point game
oracle, including Mealy/Moore causality, late assumption failure, initial/preset
independence, nonterminating acceptance, and the byte-identical official
`amba_decomposed_shift.tlsf` input. These tests specify the intended behavior;
server qualification results are recorded separately.
