# Upstream corpus — PDDL

Unmodified `.pddl` files from **AI-Planning/pddl**, `tests/fixtures/pddl_files/`
— six IPC domains with one problem each, vendored as PAIRS.

- Source: https://github.com/AI-Planning/pddl/tree/main/tests/fixtures/pddl_files
- Retrieved: 2026-08-17
- Licence: MIT (AI-Planning). Unmodified.

Domains: `acrobatics`, `beam-walk`, `blocksworld-ipc08`, `childsnack`, `doors`,
`elevators`. These are International Planning Competition domains, so they are
the planning community's own files rather than a reader's test set.

**Vendored in pairs on purpose.** A PDDL domain is a *schema*: the problem
supplies the objects that turn it into a concrete transition system, so running
a domain alone measures nothing. `test_upstream_corpus.cpp` has a `PLANNING`
shape that pairs `<case>_domain.pddl` with the problem beside it and sets a
`plan_horizon`.

## 0 of 6, and the corpus found a silent drop

**An unrecognised effect head was being added as a FLUENT.** The effect handler
knew `and`, `not`, `when` and `forall`, and anything else fell through to
`adds.push_back(atomName(head, ...))` — so a construct nobody had implemented
became an atom in the model. It surfaced only later, and badly, as
`E_TYPE: undeclared identifier 'oneof__@1'`: a mangled name, pointing at a
symbol the file never wrote.

**Had the head collided with a declared predicate it would not have surfaced at
all**, and the model would have been quietly wrong. That is the failure mode
this project is organised against, and it took someone else's files to reach it.

## What the six are

Four use **`oneof`**, which is FOND non-determinism: the action has several
possible outcomes and the environment picks. That is not a harder planning
problem, it is a **different question** — a solution is a policy rather than a
plan, and "is there a plan" becomes "is there a strategy against an adversary".
Refused by name.

**`=` is now implemented**, and exactly rather than approximately: both sides of
`(= ?x ?y)` are object terms, and after the action's parameters are substituted
both are ground object *names*, so the atom is true precisely when the names are
the same. PDDL objects are distinct constants, so two names denote one object iff
they are one name — that is equality, not an encoding of it. `blocksworld-ipc08`
consequently moved from `=` to `oneof`.

**The corpus itself is the problem, and it is mine.** Five of these six domains
are FOND, so five of the six refusals are `oneof` — and `oneof` asks a different
question rather than a harder one. A corpus that is 5/6 non-deterministic reports
almost nothing about classical planning, which is what this frontend implements.

I sampled by directory name without checking determinism. **It should be
re-sampled toward classical domains** — `barman-sequential-optimal`,
`cave-diving-sequential-optimal`, `block-grouping`, `depots-numeric-automatic`
are all in the same fixture tree — and the attempt to do so hit
`raw.githubusercontent` rate limiting (HTTP 429). Until then this corpus's honest
reading is "the FOND refusal works and nothing else has been measured".

`childsnack` reports an undeclared identifier for an atom in its `:init`, and is
the one genuine loose end among the six.
