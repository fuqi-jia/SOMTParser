# `TransitionSystem` — a design note, for your decision

**Date**: 2026-08-14
**Status**: **proposal. No code has been written against it.**
**Blocks**: BTOR2, AIGER, VMT-LIB, MoXI (cluster D) — and PDDL, which needs the same shape
for a different reason.

Four language documents independently arrived at the same three names —
`TransitionSystem`, `ExprKind::NEXT`, and a BMC unrolling pass recording
`Bound::BMC_DEPTH` — so this is not a design choice so much as a design that four formats
have already made. What is left to decide is where it lives and how much of it is
representation rather than pass.

I am writing this instead of building it because it changes `ConstraintModel`'s contract,
and every frontend and pass in tree is written against that contract.

---

## 1. The problem in one line

**`ConstraintModel` is one query. A transition system is a family of them.**

A BTOR2, AIGER, VMT-LIB or MoXI file does not describe a set of constraints with a
satisfying assignment. It describes a machine:

| Part | What it is | Example |
|---|---|---|
| state variables | the machine's memory | `s`, `s'` |
| **init** | which states it may start in | `s = 0` |
| **trans** | which steps it may take | `s' = s + 1` |
| **property** | what must always hold | `s < 10` |

The question is *"can the property be violated by any reachable state"*, and no assignment
answers it: the answer is about an unbounded sequence of steps. Handing these four parts to
an SMT solver as four constraints asks something else entirely — it asks whether one state
satisfies all four at once, which is neither necessary nor sufficient for the real question.

**This is a second-filter question** (`docs/languages-scoping.md` §6): does translating the
format answer the question the competition asks? For cluster D the answer is *only after an
unrolling decision*, and the decision has a bound attached.

---

## 2. What the four documents already agree on

| Name | Proposed by | What it holds |
|---|---|---|
| `TransitionSystem` | btor2.md §5, aiger.md §5, vmt-lib.md §5, moxi.md §5, pddl.md §5 | init, trans, property, and the state variables |
| `ExprKind::NEXT` | the same four | `s'` — the value of a state variable *after* the step |
| `Bound::BMC_DEPTH` | the same four | **already exists** in `Fidelity::Bound::Kind` |
| `SubsystemInst` | moxi.md §5 only | MoXI's `:subsys` hierarchy |

`Bound::BMC_DEPTH` existing already is the useful signal: the fidelity lattice was built
expecting this, and no lattice work is needed.

---

## 3. The proposal

### 3.1 Representation

```
struct TransitionSystem {
    std::vector<VarDecl> state;        // the machine's memory
    ExprPtr init;                      // over state
    ExprPtr trans;                     // over state and NEXT(state)
    std::vector<Property> properties;  // each over state
};

struct Property {
    std::string name;
    ExprPtr     formula;               // must hold in every reachable state
    enum Kind { INVARIANT, LIVENESS } kind = INVARIANT;
};
```

`ExprKind::NEXT` wraps exactly one `IDENT` naming a state variable. It is deliberately not a
general operator: `NEXT(NEXT(s))` is not a thing these formats can say, and allowing it would
put a term in the IR that no frontend produces and no pass knows how to unroll.

**Where it lives** — this is the part I want your call on:

| Option | Shape | Cost |
|---|---|---|
| **A. A field on `ConstraintModel`** | `std::optional<TransitionSystem> system;` alongside `decls`/`constraints`/`objectives` | every consumer must ask "is this a system or a query"; the two are never both present, so the type permits states that cannot occur |
| **B. A sibling type, with `Translation` holding either** | `ConstraintModel` unchanged; `TransitionSystem` a peer | the frontend contract changes shape (`ParseOutcome` gains a second product), and `translate()` grows a branch |
| **C. Systems are lowered to a `ConstraintModel` by a pass, and never reach a consumer** | the unrolling pass IS the translation; `TransitionSystem` is internal to it | no consumer changes at all; but the report cannot say the input was a system, only that a `BMC_DEPTH` bound applies |

**My recommendation is B**, and the reason is the paper's claim rather than the code. Under
A, a consumer that forgets to check the optional silently treats a machine as a query. Under
C, the *fact that the input was a transition system* is not in the record — and "we unrolled
a machine to depth k" is exactly the kind of thing per-instance recorded fidelity exists to
say. B makes the distinction a type, which is the one place it cannot be forgotten.

### 3.2 The unrolling pass

```
unroll(system, k) -> ConstraintModel
```

with `k` copies of the state variables, `init` at step 0, `trans` between consecutive steps,
and the property's negation asserted somewhere in 0..k. It records
`Fidelity::underApprox(Bound{BMC_DEPTH, k, <system name>})`.

**The direction of the approximation matters and is easy to get backwards.** A BMC run finds
*counterexamples*; it does not prove safety. So:

- an `unsat` at depth k means **no counterexample within k steps** — not "safe";
- a `sat` at depth k is a **real counterexample** and is directly comparable to the
  competition's answer.

That is `complete = false, sound = true` — the under-approximation direction — and it is the
same shape as `chc-comp.md` §4.1's bounded unrolling and `btor2.md` §4.2. **Reporting a
bounded no-counterexample result as "safe" would be wrong twice over**, and the verdict
naming must not reuse the competition's words for the translated question.

### 3.3 What `k` should be

I do not think this should have a default. `btor2.md` §4.3 calls the two silent defaults out
by name, and a depth chosen by the frontend is precisely one of them: every instance is then
measured at a bound nobody recorded choosing. It should come from `TranslateOptions`, and an
instance translated without one should be refused rather than translated at a guess.

---

## 4. What I would build, in order

1. `TransitionSystem`, `Property`, `ExprKind::NEXT`, and the type-checker rules for them —
   `NEXT` only in `trans`, only around a state variable.
2. The unrolling pass, with the fidelity direction above, and a property test: unrolling to
   depth k and to depth k+1 must give scripts that differ, and a system whose property is
   violated at step j must produce a satisfiable script for every k ≥ j.
3. **BTOR2 first**, because it is the format with the least syntax between the file and the
   four parts, so a bug is a bug in the shape rather than in a reader.
4. AIGER, which is BTOR2 with one-bit words and no arrays.
5. VMT-LIB, which is SMT-LIB 2 with annotations — so it reuses `ParserToHir` the way CHC-COMP
   and the SMT-LIB baseline do.
6. MoXI, last, because `:subsys` needs a flattening pass that nothing else in the batch
   needs.

PDDL is a separate decision and is **not** on this list: it needs the same shape but its
bound is a plan horizon rather than a BMC depth, and `Fidelity::Bound::Kind` has no
`PLAN_HORIZON`. See `docs/open-questions-2026-08-13.md`.

---

## 5. What I want from you

1. **A, B or C** for where `TransitionSystem` lives. I recommend B.
2. Whether `k` may have a default. I recommend not.
3. Whether liveness is in scope at all. `btor2.md` §4.5 says it is a *different* problem
   rather than a harder one, and I would leave `Property::LIVENESS` declared and refused —
   so a liveness instance is named rather than silently translated as an invariant, which is
   the wrong question with the right shape.
