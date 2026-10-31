# The solving and counting API

This guide describes the Python `Formula`, `Result`, and backend-binding API,
including `sp.read` and `sp.sweep`. It follows the shipped implementation;
examples that invoke a solver or counter require the corresponding executable
and are not installation checks.

---

## 1. `sp.read()`: a `Formula`, and what it costs to ask about it

```python
import somtparser as sp

f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2")
repr(f)
# 'Formula(smtlib2, 1 constraints, fidelity=count-unassessed)'
```

`sp.read` wraps the existing `sp.translate()` — same C++ `Translation`
underneath, same `--options` channel, same `strict` behaviour (`sp.read`
always translates with `strict=True`, so a translation failure raises
`TranslationError` there and then, not on first use). Nothing about
`sp.translate()` changed; `sp.read()` is a second, thinner entry point onto
it.

A `Formula` is a translation plus (once bound) a backend. Everything that
requires no solving is a cheap property, in the spirit of `.shape` / `.dtype`:

```python
f.language                       # 'smtlib2' -- the id used, or detection's answer
f.fidelity.sound                 # True
f.fidelity.count_status          # 'unassessed' -- no count claim was recorded
f.fidelity.preserves_count       # False -- derived; also false for no_guarantee
f.features                       # {'int-var': 1, ...} -- HIR feature -> count
f.stats.num_constraints          # 1
f.backend                        # None -- nothing bound yet
```

`f.language` is worth a second look: when the caller names a language, that
name comes back; when detection chose one (`sp.read(path)` with no
`language=`), the *detected* id comes back, not the literal string `"auto"`.
A sweep over a mixed corpus groups its results by this field, and a column
that read `"auto"` for every detected file would lose exactly the
distinction it exists to record.

`repr(f)` reports `exact`, `count-unassessed`, or `approximate`. `exact` means
sound, complete, optimum-preserving, count-preserved, and without bounds.
`count-unassessed` means the other fidelity axes are exact but no count status
was recorded; `approximate` includes a `no_guarantee` count status. In C++,
`Fidelity::exact()` initializes the pre-count fidelity axes and leaves
`count_status` at its conservative `UNASSESSED` default. The repr reports
`exact` only when count preservation is also recorded. The read-only Python
`preserves_count` property is derived from `count_status == "preserved"`; a
false value alone does not distinguish `unassessed` from `no_guarantee`. Once a
backend is bound, the repr grows a `backend=...` suffix:

```python
g = f.to("z3")
repr(g)
# 'Formula(smtlib2, 1 constraints, fidelity=count-unassessed, backend=z3)'
```

A `Formula` that failed to translate (see `sp.sweep`, §8) has no underlying
`Translation`, and every property that needs one raises `TranslationError`
rather than an unqualified `AttributeError` on `None` — `repr()` alone stays
safe to call, because printing a failed item is how a sweep is inspected:

```python
# repr(failed_formula) -> "Formula(dimacs, FAILED: <first line of the error>)"
```

---

## 2. `.to()`: binding a backend, and doing nothing else

`.to()` returns a **new** `Formula` wrapper bound to the named backend and
does no backend work. The wrapper shares the existing translated model with
the original; it does not copy or retranslate that model. Binding options are
wrapper state, so rebinding does not alter the original object's backend,
timeout, path, or arguments.

```python
f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2")
g = f.to("z3", timeout=10)
g is f                # False
f.backend              # None -- the original is untouched
g.backend               # 'z3'
```

The backend **name** is validated immediately — `f.to("frobnicate")` raises
`BackendNotFound` naming the typo right where it was made:

```python
f.to("frobnicate")
# BackendNotFound: unknown backend 'frobnicate'; this build knows: cvc5, d4,
# ganak, optimathsat, smtlib, z3
```

The backend's **binary**, by contrast, is deliberately *not* looked for at
`.to()` time — whether a solver is installed is a fact about the machine
running the code, not about the formula, and belongs to the call that
actually needs the binary (`.solve()`, `.optimize()`, `.count()`):

```python
h = f.to("cvc5")        # cvc5 need not be installed; this does not raise
h.backend                # 'cvc5'
h.solve()                # *this* is where BackendNotFound would raise, if cvc5 were missing
```

`timeout`, `path` and `args` are **cumulative** across re-binding — the same
choice torch makes for `.to()`'s dtype/device arguments. Re-binding to a
different backend keeps a timeout you already set, because silently dropping
a caller's limit turns an instance that should report `unknown` into one
that hangs a batch:

```python
f.to("z3", timeout=5).to("cvc5")._timeout    # 5 -- kept, not reset
f.to("z3", timeout=5).to("cvc5", timeout=1)._timeout  # 1 -- explicit still wins
```

`path`, unlike `timeout`, almost always *should* be overridden on a rebind,
since it names a binary for the backend you were just bound to — carrying it
forward blindly would point the new backend at the old one's executable.

`.script()` renders the formula's SMT/OMT text in the **bound backend's
dialect** (`SmtLib2025` if nothing is bound):

```python
f.to("z3").script()
# '(set-logic ALL)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)\n(exit)\n'
```

Binding the backend is what makes a dialect mismatch *unrepresentable*.
Before this API existed, a caller could render OptiMathSAT's multi-objective
syntax and hand it to z3 — which is exactly the defect behind two
`instances/ok/` fixtures that failed under the default dialect on
2026-09-20. The regression guard for this is in
`test/python/test_solving_api.py::test_backend_selects_the_dialect`:
rendering the same multi-objective source through `.to("z3").script()`
produces `(set-option :opt.priority lex)`, and through
`.to("smtlib").script()` produces `define-multi-objective` — the same
formula, two different, backend-appropriate texts.

---

## 3. The backend table

`python/somtparser/_backends.py`'s `BACKENDS` registry, as shipped:

| name | binary | dialect | reads | install hint |
|---|---|---|---|---|
| `z3` | `z3` | `Z3` | smt | `pip install z3-solver`, or install the `z3` binary |
| `cvc5` | `cvc5` | `Z3` | smt | see https://cvc5.github.io for a binary release |
| `optimathsat` | `optimathsat` | `OptiMathSAT` | smt | see https://optimathsat.disi.unitn.it |
| `smtlib` | *(none)* | `SmtLib2025` | smt | text-only — "no solver reads it yet" |
| `d4` | `d4` | `NONE` | count | see https://github.com/crillab/d4 |
| `ganak` | `ganak` | `NONE` | count | see https://github.com/meelgroup/ganak |

Two things worth knowing before reading further:

- **`smtlib` has no binary on purpose.** It exists to *emit* the SMT-LIB 2025
  proposal syntax — the argument for having the dialect at all is that it is
  standardised benchmark text, and nothing implements it yet to solve
  against. `.to("smtlib").script()` works; `.to("smtlib").solve()` raises
  `BackendNotFound`, the same as any other backend with no binary found.
- **`d4` and `ganak`'s `args` are declared from their published documentation
  and have not been verified against a running binary.** `.to(name,
  args=[...])` overrides the declared argv, so a caller with a different build
  of either can correct the invocation without editing the registry.

A binary is looked for on `PATH` first, then beside the running Python
interpreter (`os.path.dirname(sys.executable)`). The second lookup exists
because `pip install z3-solver` puts its binary next to the interpreter, on
`PATH` only when the venv is *activated* — and a recipe that invokes pytest
by absolute path never activates it. Missing this lookup is what silently
skipped 41 solver-backed tests on 2026-09-20; `backend_path()` checks
`os.access(path, os.X_OK)` rather than `os.path.exists`, so a same-named
directory (which satisfies `exists`) is correctly reported as "not found"
rather than handed to `subprocess.run`, which would raise
`IsADirectoryError` instead of the one specific, explaining exception this
API promises.

`backend_path(name)` never raises for an unknown name — it returns `None` —
so a test's `@pytest.mark.skipif(sp.backend_path("z3") is None, ...)` can ask
about a backend that does not exist without that becoming its own error.

---

## 4. Asking questions: `.solve()`, `.optimize()`, `.value()`

```python
f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2").to("z3")
r = f.solve()
r          # Result(sat, 0.018s)
r.status   # 'sat'
```

`Result` is a frozen dataclass: `status` (`"sat"` / `"unsat"` / `"unknown"`),
`seconds`, `reason` (qualifies `"unknown"`: `"timeout"` or a truncated
`"crash: ..."`), `model`, `count`, and the raw `stdout`. Its `repr` shows only
`status`, `reason`, `count` (if any) and the elapsed time — not the raw
solver text, which can be long or empty.

**Read `.model` literally, not as a parsed structure.** `.script()` renders
`(check-sat)(exit)` with no trailing `(get-model)` (`.optimize()` adds
`(get-objectives)` for itself; `.solve()` adds nothing), so
for `z3 -in` today `.model` is the solver's stdout *after* the status line —
which, for the plain examples above, is the empty string: z3 in this mode
prints exactly `sat` and nothing else unless the script itself asked for
more. `.model` is not a `dict`; it is whatever text follows the status line,
verbatim.

`.optimize()` sends the objectives — they are already in the script, in the
bound backend's dialect — and additionally asks `(get-objectives)` after the
check, which `.script()` alone does not. That difference is not cosmetic: a
solver that finds an optimum does not print it unless asked, so for a while
`.optimize()` and `.solve()` really were the same call and `.value()`
returned the empty string for every successful optimisation while its
docstring promised a number. The separate method name also says which
question was asked, which is what gets checked against the fidelity record:

```python
f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)"
                   "(assert (>= x 3))(minimize x)", language="smtlib2")
r = f.to("z3").optimize()
r.status                     # 'sat'
r.objectives                 # {'x': 3}
```

```python
f.optimize()
# raises FidelityError if f.fidelity.preserves_optimum is False, naming the
# recorded Bound (or "no bound was recorded" if none was)
```

`.value()` is the `.item()` of this API — the single objective's value:

```python
f.to("z3").value()    # 3
```

It returns `None` when the backend reported anything other than `sat`, and
raises rather than returning `None` in the two cases where `None` would be
ambiguous: a model that declares **no** objective (there is nothing to have a
value, which is a different answer from "the value is unknown"), and one that
declares **several** (then "the" value is not defined — read
`Result.objectives` instead). Values are `int` when the backend printed a
plain integer and its own text otherwise, because an optimum is legitimately
`oo`, `(- oo)` or a rational, and coercing those would either fail or lie.

**A model counter cannot answer either method, and both refuse rather than
mislabel the answer.** A counter's stdout is a number, and `.solve()` handing
that back as `Result(status="sat", model="1024")` would read as "satisfiable,
here is the witness" — a different claim from "there are 1024 models", one a
caller reading `.model` could never tell apart from a real witness:

```python
sp.read(source="p cnf 2 1\n1 2 0\n", language="dimacs").to("d4").solve()
# BackendNotFound: 'd4' is a model counter, not a solver: it reports how
# many models exist, not whether one does. Call .count() instead, or bind a
# solver with .to('z3').
```

`.optimize()` refuses the same case with its *own* message — naming what an
optimising query needs, not the message `.solve()` would give, which points
at `.count()`: that would answer a different question from the one
`.optimize()` asked.

---

## 5. `.count()` and the fidelity gate

This is the method the whole axis exists for. A translation can preserve
satisfiability perfectly in both directions and still change *how many*
models there are — an auxiliary variable that is only one-sidedly implied by
what it guards is free to take either value whenever the guard holds, which
doubles the count per such variable while leaving every SAT/UNSAT answer
correct. The API exposes this as a tri-state `Fidelity.count_status`:
`"unassessed"` by default, `"preserved"` when the translation records a
one-to-one model correspondence, or `"no_guarantee"` when it makes no such
promise. The compatibility property `preserves_count` is true only for
`"preserved"`; false also includes the unassessed case.

In C++, read the compatibility Boolean through
`Fidelity::preservesCount()`; the old writable `preserves_count` field is no
longer the API. Python exposes `preserves_count` as a read-only derived
property. Use `count_status` when the distinction between `unassessed`,
`preserved`, and `no_guarantee` matters. A status is the recorded contract, not
an independent proof of the claim.

```python
c = sp.read(source="p cnf 2 1\n1 2 0\n", language="dimacs")
c.fidelity.count_status          # 'unassessed' -- default absent an explicit claim
c.fidelity.preserves_count       # False -- derived Boolean, not a third status
c.cnf()                          # DIMACS for the target formula; no counter runs
# c.to("d4").count(scope="target")  # target assignment count, if d4 is installed
```

The source scope is the default. It refuses both an unassessed translation
and one that makes no count-preservation guarantee; neither status is silently
treated as a preserved source count:

```python
b = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2", profile="bv32")   # bv32 bounds the unbounded Int
b.fidelity.count_status          # 'no_guarantee'
b.fidelity.preserves_count       # False
b.to("d4").count()               # FidelityError before any counter is invoked
# Message begins: this translation provides no count-preservation guarantee;
# counting the target is not established to count the source's models.
# Pass scope='target' to count the target anyway.
```

When present, `Fidelity.bounds` still reports limits by `kind` (`BV_WIDTH`,
`BMC_DEPTH`, `DOMAIN_CUT`, `HORN_UNROLL`, `PLAN_HORIZON`, …), `value`, and
`site`. A status is not inferred from a bound's presence: the status is
recorded separately.

`Fidelity::equisat()` records `count_status == "no_guarantee"`: its name
promises equisatisfiability, not equal model cardinality. Bounded and relaxed
translations likewise make no count-preservation promise. The status remains
independent of soundness, completeness, and optimum preservation.
Do not infer source-count preservation from one successful sample or from
satisfiability agreement. Inspect the status and the evidence recorded for the
specific translation contract.

A `"preserved"` claim is a contract assertion and requires count-evidence
metadata at the relevant encoding choice or `MODEL_COUNT` obligation. The
metadata records an evidence kind, rationale, and references. Contract
validation checks that these fields are present; it does not dereference the
references, validate a proof, or rerun tests. Neither `count_status ==
"preserved"` nor the presence of metadata independently proves a bijection.
The evidence record is provenance, not a proof checker.

### `scope="target"`

Knowingly asking for the target's count is legitimate; silently being handed
it as a source count is not. `.count(scope="target")` bypasses only the
source-fidelity gate:

```python
b.to("d4").count(scope="source")  # -> FidelityError, before a counter is invoked
b.to("d4").count(scope="target")  # passes gate, then checks DIMACS support
```

For a supported Boolean target, `scope="target"` can proceed to a counting
backend if one is installed. It counts the target assignment space, not the
source's models. For the bounded-`Int` example above, the scope gate is passed
but DIMACS conversion refuses the non-Boolean variable. This separates two
questions: whether the translation preserves source counts, and whether the
target formula can be represented by the propositional counter.

The counter path refuses weighted or projected count headers rather than
silently returning an unweighted or unprojected number. `.cnf()` also refuses
non-Boolean variables, function declarations or recursive definitions,
uninterpreted sorts (including unused declarations), quantifiers, source
parser temporaries outside the declared Boolean vocabulary, and theory atoms
that Tseitin would replace by unconstrained Boolean abstractions. A translated
SMT-LIB `define-fun` is not assumed countable merely because its source has a
definition: the translation currently carries function signatures through HIR
as declarations, so the Boolean assignment encoding refuses them.

`.count()` also validates its `scope` argument itself:

```python
c.to("d4").count(scope="sideways")   # ValueError: scope must be one of
                                      # ('source', 'target'), not 'sideways'
```

---

## 6. `.cnf()`: the DIMACS emitter behind counting

Counting backends read DIMACS, not SMT-LIB — `d4` and `ganak` take a file
path on argv, not a script on stdin — so `.count()` needs a different
rendering from `.solve()`/`.optimize()`. `.cnf()` produces it, via the
parser's own `to_tseitin_cnf`, and is what `test/python/test_counting_api.py`
exercises as **text**, needing no counter binary at all:

```python
c = sp.read(source="p cnf 2 1\n1 2 0\n", language="dimacs")
c.cnf()
# 'p cnf 3 4\n3 -1 0\n3 -2 0\n1 2 -3 0\n3 0\n'
```

The following invariants are useful when reading that output. `.to()` only validates
and records the backend name; it does not look up the executable, so this
check does not require `d4` to be installed:

```python
f = sp.read(source="""(set-logic QF_UF)
(declare-const w Bool)
(declare-const a Bool)
(declare-const b Bool)
(assert (or w (and a b)))""", language="smtlib2")
first = f.cnf()
bound = f.to("d4")
assert bound.cnf() == first
assert f.cnf() == first
```


- **Tseitin, not distribution**, because a distributive normal form is
  exponential — and because the two-sided gate clauses functionally determine
  each auxiliary from the target formula's Boolean variables. Counting all
  DIMACS variables therefore gives the supported propositional target
  formula's satisfying-assignment count without projection. That is a target
  assignment count; it is a source-model count only when the source-to-target
  mapping is actually bijective and that contract is recorded separately.
  `count_status == "preserved"` is the recorded claim, not proof of the
  bijection. Required count-evidence metadata validates its completeness and
  provenance but does not independently validate the argument.

  That was not true of every gate when this was first written. The
  implication gate's definition emitted a converse clause encoding
  `(a and b) -> c` where `(a -> b) -> c` was needed, so `c` was free whenever
  `a` was false and a nested `(=> a b)` multiplied the count — equisatisfiably,
  which is why satisfiability testing never saw it. Separately, the evaluator
  read `(=> a b c)` as `a -> b`, dropping every argument past the second. Both
  are fixed.

  The regression suite includes formula-level checks, random DIMACS samples,
  and generated formulas for the Boolean gates. The third class exists because
  the DIMACS-only sample grammar cannot expose a bug in nested gate encodings:
  `test/regression/test_tseitin_counts_models.cpp` counts a small formula
  against its Tseitin CNF for each gate in a NESTED position (at the root the
  assertion pins the gate's variable and nothing is observable);
  `test_the_emitted_cnf_has_the_source_model_count` and
  `test_cnf_preserves_the_count_over_random_formulas` sample 120 random
  DIMACS files; and
  `test_cnf_preserves_the_count_over_random_formulas_of_every_gate` samples
  random *formulas*. The DIMACS generator was believed to be the property
  test that made the count claim safe, and it could not be: the only
  connective a DIMACS file has is a disjunction of literals, so its sample
  space excluded every gate that could be wrong. A randomised test is only as
  good as the grammar it samples.
- **Repeated `.cnf()` calls do not accumulate Tseitin state.** `.to()` creates
  a new wrapper around the same translation, so bound siblings share the
  underlying model. For each `.cnf()` call, the implementation serializes the
  accepted Boolean parser and converts it in a fresh parser, then checks the
  ordered `(name, sort)` variable vocabulary and assertion count. This is a
  serialization sanity check, not a proof of semantic equivalence. This keeps a
  second call or a call through a `.to()` sibling from counting stale
  auxiliaries. A declared source name such as `temp_0` remains part of the
  source vocabulary and does not collide with generated Tseitin variables.
- **A declared variable with no clause still counts.** DIMACS' own invariant
  is that the file's vocabulary is the header's `VARIABLES`, not whatever the
  clauses happen to mention — a variable that occurs in no clause is still
  free, and a free Boolean variable doubles the model count. A file with no
  clauses at all is the sharpest case: `p cnf 2 0` has **4** target assignments,
  not 1. `.cnf()` retains those declared but unused Boolean variables in the
  DIMACS header. This target-vocabulary statement is independent of whether the
  source translation has a
  recorded `PRESERVED` source-count contract. A historical bug returned
  `p cnf 0 0` for clause-free formulas and was exposed by differential tests,
  not by
  any of nine hand-written cases tried first (see
  `docs/continuation-worklog-2026-09-18.md`, the entry for this plan's
  landing). Verify it stayed fixed:

  ```python
  text = sp.read(source="p cnf 2 0\n", language="dimacs").cnf()
  text.splitlines()[0]   # 'p cnf 2 0' -- not 'p cnf 0 0'
  ```

`.cnf()` refuses, by name and sort, rather than silently bit-blasting a
theory formula — a DIMACS counter has no theories, and translating one into
DIMACS is not a thing this method does:

```python
sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
        language="smtlib2").cnf()
# NotImplementedError: cannot emit DIMACS: 1 variable(s) are not Boolean
# (x:Int). A DIMACS counter has no theories, and bit-blasting is a
# translation this does not do.
```

---

## 7. The error taxonomy

These failures belong to different layers; preserving those distinctions
lets a batch record refusals without mistaking them for solver outcomes:

```
BackendNotFound(name, hint)          solver/counter absent, name typo'd,    -> exception
                                     or a backend asked the wrong question
FidelityError(message)               source count is unassessed / not       -> exception
                                     guaranteed; optimum is not preserved;
                                     Set API contract is unsupported; or
                                     requested objective value is undefined
NotImplementedError(what, why)       a target operation is outside the     -> exception
                                     supported propositional/count scope
ValueError(scope)                    count scope is not source or target    -> exception
Result(status="unknown",
       reason="timeout"|"crash: …")  a real, legitimate outcome             -> data
```

`NotImplementedError` is the *refusal by name* this project's invariant 9
requires, at the API layer: the request makes sense, nothing is wrong with the
input, and answering would mean answering a different question. It is raised
when `.cnf()` meets a function interpretation, an uninterpreted sort, a
non-Boolean variable, a theory atom that Tseitin would replace with an
unconstrained Boolean abstraction, or a quantifier; and when `.count()` is
asked about an instance whose `c p weight` or `c p show` headers declare a
weighted or projected count, which the frontend reads and records but nothing
downstream applies yet. Each names what it found.

A **timeout is data**, not an exception, because a batch over hundreds of
files must not stop for one slow instance:

```python
f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2").to("z3", timeout=0.001)
f.solve()
# Result(unknown, timeout, 0.003s)   -- or, occasionally, still Result(sat, ...)
#                                        if z3 answers inside 1ms
```

A **missing backend** and a **fidelity violation**, by contrast, are
exceptions: continuing past either produces a number or an answer that means
something other than what it claims to mean, which is the failure mode this
whole project is organised against. `BackendNotFound` is also what an
unknown backend *name* raises (`.to("frobnicate")`, §2), what
`.solve()`/`.optimize()` raise when asked of a counting backend, and what
`.count()` raises when asked of a solver (§4) — one exception type covers
"this backend cannot answer this" in every sense of "cannot". Each of those
three names the method that *can*: a counter asked to solve is told to call
`.count()`, a solver asked to count is told to bind `d4`.

`.optimize()` also raises `FidelityError` before invoking a solver when
`preserves_optimum` is false; a source-count guarantee does not substitute for
an optimum guarantee. Set-valued formulas have a separate backend contract:
the current Set API requires cvc5's Sets extension, refuses non-cvc5 backends
and explicit arguments that disable `--sets-exp`, and adds that option when
needed. Quantified finite sets over infinite or unknown carriers are refused
rather than sent as if they had an exact semantics. These are API contract
refusals, not claims about whether a particular solver binary is installed.

A subprocess that exits with a code other than `0`, `10` or `20` (the
SAT-competition sat/unsat conventions) is reported as
`Result(status="unknown", reason="crash: <first 200 chars of stderr>")` — data
again, not an exception, on the same reasoning as a timeout: a batch should
see a crashed instance as a result to log, not a reason to stop.

---

## 8. The batch layer: `sweep`, `profile`, `seed`

Thin by design — the same core with scoped defaults applied, because an
interactive run and a batch run must not be able to disagree about what a
profile means.

```python
with sp.profile("bmc", bmc_depth=10):
    for f in sp.sweep("languages/*/instances/upstream/*"):
        r = f.to("z3", timeout=10).solve()
        print(f.language, f.fidelity.count_status, r.status, r.seconds)
```

`sp.profile(name, **options)` is the `with torch.no_grad(): ...` shape — a
default that applies to every `sp.read()` (and hence every `sp.sweep()`)
inside the block and is gone the moment it ends, so one batch cannot leak a
setting into the next:

```python
with sp.profile("bv32"):
    sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
            language="smtlib2").fidelity.count_status      # 'no_guarantee'
sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
        language="smtlib2").fidelity.count_status          # 'unassessed' -- default
```

`sp.seed(n)` records a seed that flows onto every `Formula` read afterwards
(`f.seed`) and, when the bound backend declares a `seed_flag`, onto its
argv (`z3`: `smt.random_seed=`, `cvc5`: `--seed=`). `sp.seed(None)` clears
it. Both `profile` and `seed` are **thread-local**, deliberately — a sweep
running in one thread cannot change what `sp.read()` means in another.

`sp.sweep(pattern)` globs `pattern` and yields one `Formula` per match,
**sorted**, so the order is reproducible across runs. A file that fails to
translate is *yielded with `.error` set*, not raised — the whole point being
that a sweep over a corpus that stopped at the first refusal would measure
nothing, and a refusal is itself a result worth counting:

```python
found = list(sp.sweep("languages/dimacs/instances/reject/*"))
all(f.error is not None for f in found)                       # True
all(isinstance(f.error, sp.TranslationError) for f in found)  # True
"FAILED" in repr(found[0])                                    # True -- printable
```

**`sp.sweep(...)` resolves its scope where it is written, not where it is
iterated.** `sweep` is a plain function, not a generator function: it reads
`sp.profile()`'s and `sp.seed()`'s scoped defaults and runs `glob()`
immediately, at the call, and only the per-file reading is the (inner)
generator it returns. That matters because storing a sweep and iterating it
later is an ordinary thing to write:

```python
pattern = "languages/dimacs/instances/ok/*"
with sp.profile("bv32"):
    stored = sp.sweep(pattern)          # resolved to "bv32" HERE, at this call
{f.translation.report.provenance.profile_id for f in stored}   # {'bv32'}

plain = list(sp.sweep(pattern))         # no scope in effect -> "default"
{f.translation.report.provenance.profile_id for f in plain}    # {'default'}
```

Had `sweep` instead been written the obvious way — a `def` containing `yield`
— none of its body would run until the first `next()`, so `stored` above
would have silently read every file under `default`: provenance would still
have honestly recorded `default`, because `default` is what ran, which is
exactly what would have made the mistake hard to notice. `sp.read()` is what
makes the fix possible: it now takes explicit `options=` and `seed=` keyword
arguments that *override* the scoped defaults rather than reading them
(`seed=None` is a real value — it clears the seed — so the parameter's
unset default is a private sentinel, not `None`). `sweep` resolves the
ambient profile, options and seed exactly once, at its own call, and passes
that one resolution into every `read()` it makes internally, rather than
letting each file's `read()` re-consult whatever happens to be scoped at the
moment that file is reached.

---

## 9. What torch has that this deliberately does not

The API borrows `.to()`'s type semantics, `.shape`/`.dtype`-style cheap
properties, an informative `repr`, `torch.load` (`sp.read`), `DataLoader`
(`sp.sweep`), `with torch.no_grad(): ...` (`sp.profile`), `.item()`
(`.value()`), and `torch.manual_seed` (`sp.seed`). Left out, on purpose:

| torch has | this does not, because |
|---|---|
| `.cuda()` / `.cpu()` shorthands | there will eventually be a dozen backends; per-backend shorthand methods only scatter, where `.to(name)` already generalises |
| `nn.Module` / `forward` | nothing here composes in layers — a `Formula` is a leaf, not a graph of them |
| `.detach()` / autograd | no counterpart: there is no gradient to detach from |
| `torch.nn.functional` | the existing `HirBuilder` already is the "build a formula programmatically" surface; a second one would duplicate it rather than complement it |

---

## Further reading

- `docs/superpowers/specs/2026-09-20-counting-and-solving-api-design.md` — design rationale.
- `include/somtparser/translation/fidelity.h` — the `Fidelity` lattice itself, and the
  four constructors' comments on exactly what each one claims.
- `docs/languages/dimacs-cnf.md` §3 (Construct → HIR mapping) and
  `docs/languages/opb-wbo.md` — the two frontends whose corpus made the axis
  testable: DIMACS's `c t` / `c p weight` / `c p show` headers, and OPB's WBO
  threshold relaxation.
- `test/python/test_solving_api.py`, `test/python/test_counting_api.py`,
  `test/python/test_batch_api.py` — source for related examples.
