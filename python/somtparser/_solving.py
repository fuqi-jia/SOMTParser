"""Formula, Result, and the PyTorch-shaped surface over them.

`.to()` follows torch's type semantics: it returns the SAME type with a
different binding, does no work, and does not mutate. A formula bound to two
backends is two objects sharing one translation.
"""

from __future__ import annotations

import contextlib
import threading
from dataclasses import dataclass, field
from typing import Sequence

from . import _backends
from ._backends import BackendNotFound


class FidelityError(RuntimeError):
    """The translation does not preserve what the question asks about."""


_COUNT_SCOPES = ("source", "target")

#: Scoped defaults. Thread-local so a sweep in one thread cannot change what
#: another thread's `read` means.
_defaults = threading.local()


def _default(name, fallback=None):
    return getattr(_defaults, name, fallback)


@contextlib.contextmanager
def profile(name: str, **options):
    """Scope a profile (and frontend options) over the block.

    The `torch.no_grad()` shape: a default that applies to every `read` inside
    and is gone after, so a batch cannot leak a setting into the next one.
    """
    old_profile = _default("profile")
    old_options = _default("options", {})
    _defaults.profile = name
    # `translate()` requires a dict of strings; a caller passing e.g. an int
    # option must not have it reach the C++ boundary as one.
    _defaults.options = {**old_options, **{k: str(v) for k, v in options.items()}}
    try:
        yield
    finally:
        _defaults.profile = old_profile
        _defaults.options = old_options


def seed(n: int | None) -> None:
    """Pass a seed to backends that accept one. `None` clears it."""
    _defaults.seed = n


def _is_bool_sort(sort) -> bool:
    return str(sort).strip().lower() == "bool"


def _clause_literals(node, index):
    """The literals of one clause, or None if the clause is a tautology.

    A clause reaching here is a literal or an `or` of literals: that is what
    Tseitin produces. Anything else is a bug in the caller, not an input to
    tolerate, so it raises rather than being skipped.
    """
    parts = list(node.children) if node.is_or else [node]
    out = []
    for part in parts:
        negated = part.is_not
        atom = part.children[0] if negated else part
        name = atom.name
        if name in ("true", "false"):
            # Simplification can fold a literal to a constant.
            if (name == "true") != negated:
                return None                       # clause is satisfied
            continue                              # false literal: drop it
        if name not in index:
            raise AssertionError(
                f"clause mentions {name!r}, which is not a variable of this "
                f"formula -- to_tseitin_cnf produced a shape cnf() does not "
                f"understand"
            )
        out.append(-index[name] if negated else index[name])
    return out


def _subterms(node):
    """Every distinct subterm of @p node, memoised on identity.

    The memo is not an optimisation: hash-consing means a shared subterm is
    reachable by many paths, so a naive walk is exponential on anything CNF
    conversion has touched.
    """
    seen, out, stack = set(), [], [node]
    while stack:
        cur = stack.pop()
        key = id(cur)
        if key in seen:
            continue
        seen.add(key)
        out.append(cur)
        stack.extend(cur.children)
    return out


def _end_of_sexp(text: str, i: int) -> int:
    """Index just past the s-expression beginning at `text[i]`.

    `|quoted|` symbols are skipped whole rather than scanned, because an
    SMT-LIB symbol may legally contain parentheses and a naive depth count
    would end the expression inside one.
    """
    if text[i] == "|":
        close = text.find("|", i + 1)
        return len(text) if close < 0 else close + 1
    if text[i] != "(":
        j = i
        while j < len(text) and not text[j].isspace() and text[j] not in "()":
            j += 1
        return j
    depth, j = 0, i
    while j < len(text):
        ch = text[j]
        if ch == "|":
            close = text.find("|", j + 1)
            j = len(text) if close < 0 else close + 1
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return len(text)


def _parse_objectives(payload: str) -> dict:
    """The `(objectives (<term> <value>) ...)` block a solver prints, as a dict.

    The key is the objective TERM, and a term is not always a symbol: the
    emitter renders `(minimize (+ x y))` and the solver echoes
    `((+ x y) 5)` -- the ordinary case for a MaxSAT cost function or any
    summed objective, not an exotic one. So the term is the first BALANCED
    s-expression of the entry, not the text up to its first space. Splitting
    on the space returned `{'(+': 'x y) 5'}`, and `.value()` handed back
    `'x y) 5'` as if it were a number.

    Values stay as the backend wrote them unless they are plain integers: an
    optimum is legitimately `oo`, `(- oo)`, `(/ 1 2)` or an epsilon term, and
    coercing those would either fail or lie.
    """
    at = payload.find("(objectives")
    if at < 0:
        return {}
    body = payload[at + len("(objectives"):_end_of_sexp(payload, at) - 1]
    out = {}
    i = 0
    while i < len(body):
        if body[i].isspace():
            i += 1
            continue
        if body[i] != "(":
            break                       # malformed; keep what was read
        entry_end = _end_of_sexp(body, i)
        entry = body[i + 1:entry_end - 1]
        k = 0
        while k < len(entry) and entry[k].isspace():
            k += 1
        if k < len(entry):
            name_end = _end_of_sexp(entry, k)
            value = entry[name_end:].strip()
            try:
                out[entry[k:name_end]] = int(value)
            except ValueError:
                out[entry[k:name_end]] = value
        i = entry_end
    return out


@dataclass(frozen=True)
class Result:
    """What a backend said.

    `status` is the answer; `reason` qualifies an `unknown`. A timeout is a
    status and not an exception, because a batch over hundreds of files must
    not stop for one slow instance.
    """

    status: str                       # "sat" | "unsat" | "unknown"
    seconds: float = 0.0
    reason: str | None = None         # "timeout" | "crash: ..." for unknown
    model: str | None = None
    count: int | None = None
    #: Objective name -> value, as the backend reported them. The value is an
    #: int when it is a plain integer and the backend's own text otherwise,
    #: because an optimum can legitimately be unbounded (`oo`) or rational.
    objectives: dict = field(default_factory=dict)
    stdout: str = ""
    backend_options: tuple[str, ...] = ()
    semantic_mode: str = "native"

    def __repr__(self) -> str:
        bits = [self.status]
        if self.reason:
            bits.append(self.reason)
        if self.count is not None:
            bits.append(f"count={self.count}")
        if self.objectives:
            bits.append("obj=" + ",".join(
                f"{k}={v}" for k, v in self.objectives.items()))
        bits.append(f"{self.seconds:.3f}s")
        return f"Result({', '.join(bits)})"


def _set_solver_contract(translation):
    """Read typed source-HIR requirements without inspecting serialized SMT."""
    req = translation.set_solver_requirements
    if not req.has_sets:
        return False, "native"
    if req.has_quantifiers and req.infinite_or_unknown_carrier:
        raise FidelityError(
            "quantified finite Sets over an infinite or unknown carrier cannot "
            "be solved exactly by cvc5's quantified Set extension"
        )
    mode = "quantified-finite-carrier-sets" if req.has_quantifiers else "quantifier-free-finite-sets"
    return True, mode


class Formula:
    """A translated model, optionally bound to a backend.

    Wraps the existing `Translation` rather than replacing it: `sp.translate()`
    keeps its signature and every existing caller keeps working.
    """

    __slots__ = ("_t", "_language", "_backend", "_timeout", "_path", "_seed",
                 "_args", "_error")

    def __init__(self, translation, language, backend=None, timeout=None,
                 path=None, seed=None, args=None, error=None):
        self._t = translation
        self._language = language
        self._backend = backend
        self._timeout = timeout
        self._path = path
        self._seed = seed
        self._args = args
        self._error = error

    def _require_translation(self):
        """The underlying `Translation`, or a `TranslationError` naming why
        there isn't one.

        A sweep yields a `Formula` for a file that failed to translate rather
        than raising, and every accessor that needs the translation goes
        through here so asking such a formula a question fails by SAYING SO
        rather than with an unqualified `AttributeError` on `None`.
        """
        if self._t is None:
            from . import TranslationError
            raise TranslationError(
                f"this formula did not translate: {self._error}",
                self._error.code, self._error.diagnostics,
            ) from None
        return self._t

    # -- cheap properties, in the spirit of .shape / .dtype ------------------

    @property
    def translation(self):
        return self._require_translation()

    @property
    def language(self) -> str:
        """The language this formula was read as.

        When the caller named one, that name. When detection chose, the id it
        chose -- `"auto"` would name the mechanism rather than the answer, and
        a sweep's results are grouped by this field, so a column reading
        "auto" for every detected file loses exactly the distinction it exists
        to record.
        """
        if self._language in ("", "auto") and self._t is not None:
            detected = self._t.report.provenance.language_id
            if detected:
                return detected
        return self._language

    @property
    def backend(self) -> str | None:
        return self._backend

    @property
    def seed(self):
        return self._seed

    @property
    def error(self):
        """The diagnostic that stopped this formula translating, or None.

        A sweep yields failures rather than raising, so every item it
        produces answers this.
        """
        return self._error

    @property
    def fidelity(self):
        return self._require_translation().report.fidelity

    @property
    def features(self):
        # `TranslationReport`'s dict property is `hir_feature_counts` (see
        # python/bindings.cpp and __init__.pyi) -- not `feature_counts`.
        return dict(self._require_translation().report.hir_feature_counts)

    @property
    def stats(self):
        return self._require_translation().report.stats

    def __repr__(self) -> str:
        if self._t is None:
            # Printable rather than raising: printing one is how a caller
            # inspects a sweep.
            first_line = (str(self._error).splitlines()[0]
                          if self._error is not None else "unknown error")
            return f"Formula({self._language}, FAILED: {first_line})"
        f = self.fidelity
        if f.sound and f.complete and f.preserves_optimum and not f.bounds \
                and f.count_status == "preserved":
            shape = "exact"
        elif f.sound and f.complete and f.preserves_optimum and not f.bounds \
                and f.count_status == "unassessed":
            shape = "count-unassessed"
        else:
            shape = "approximate"
        bound = f", backend={self._backend}" if self._backend else ""
        return (f"Formula({self._language}, "
                f"{self.stats.num_constraints} constraints, "
                f"fidelity={shape}{bound})")

    # -- binding ------------------------------------------------------------

    def to(self, backend: str, *, timeout: float | None = None,
           path: str | None = None,
           args: Sequence[str] | None = None) -> "Formula":
        """Bind to a backend. Returns a NEW Formula and does no work.

        The name is validated here so a typo surfaces at the call that made it
        rather than at the solve, but the BINARY is not looked for: whether a
        solver is installed is a fact about the machine and belongs to the run.

        `args`, when given, overrides the backend's declared argv -- the
        backend arguments can vary by solver version, so a caller with a
        different build can select its invocation without editing the registry.

        `timeout`, `path` and `args` are CUMULATIVE across re-binding, the way
        torch's `.to()` is cumulative across its dtype and device arguments:
        `.to("z3", timeout=5).to("cvc5")` keeps the five seconds. Resetting
        them to the defaults on every re-bind would silently drop a limit the
        caller set, and a dropped timeout in a batch is an instance that hangs
        rather than one that reports `unknown`. Pass the value explicitly to
        change it; `path` is the one a re-bind should usually override, since
        it names a binary for the OLD backend.
        """
        _backends.spec(backend)       # raises BackendNotFound on a bad name
        return Formula(
            self._t, self._language, backend,
            self._timeout if timeout is None else timeout,
            self._path if path is None else path,
            self._seed,
            self._args if args is None else args,
            self._error)

    def script(self) -> str:
        """The text this formula would be sent as, in its backend's dialect."""
        from . import OmtDialect

        t = self._require_translation()
        if self._backend == "cvc5":
            # The backend shares the minimize/maximize command grammar, but
            # consumes native Set terms rather than Z3's array encoding.
            return t._native_smt2()
        name = _backends.spec(self._backend).dialect if self._backend else "SmtLib2025"
        try:
            return t.to_smt2(getattr(OmtDialect, name))
        except RuntimeError as error:
            if name == "Z3" and t.set_solver_requirements.has_sets:
                raise FidelityError(str(error)) from error
            raise

    # -- questions ----------------------------------------------------------

    def _require_backend(self) -> str:
        if self._backend is None:
            raise BackendNotFound(
                "no backend bound; call .to('z3') (or another backend) first"
            )
        return self._backend

    def _solver_options(self, name):
        translated = self._require_translation()
        if name == "z3" and translated.set_solver_requirements.has_sets:
            # script() performs the exact carrier checks before the backend
            # runs. cvc5's quantified-Set restrictions do not describe Z3's
            # separate, bounded Boolean-array encoding.
            return self._args, "z3-finite-set-arrays"
        requires_sets_exp, mode = _set_solver_contract(translated)
        if not requires_sets_exp:
            return self._args, mode
        if name != "cvc5":
            raise FidelityError("the Set API requires the cvc5 Sets extension or Z3 finite-set export")
        supplied = tuple(self._args if self._args is not None
                         else _backends.spec(name).args)
        if any(arg in ("--no-sets-exp", "--sets-exp=false", "--sets-exp=0")
               for arg in supplied):
            raise FidelityError("explicit cvc5 arguments disable required --sets-exp")
        enabled = any(arg in ("--sets-exp", "--sets-exp=true", "--sets-exp=1")
                      for arg in supplied)
        effective = supplied if enabled else (*supplied, "--sets-exp")
        # cvc5's default quantifier strategy may return unknown even for the
        # four possible Set Bool values. Finite model finding improves these
        # finite-carrier cases without altering the formula or bounding a sort.
        # Preserve an explicit user choice, including disabling the heuristic.
        has_fmf_choice = any(arg == "--finite-model-find"
                             or arg == "--no-finite-model-find"
                             or arg.startswith("--finite-model-find=")
                             for arg in supplied)
        if mode == "quantified-finite-carrier-sets" and not has_fmf_choice:
            effective = (*effective, "--finite-model-find")
        return effective, mode

    def _effective_backend_options(self, name, args):
        options = list(args if args is not None else _backends.spec(name).args)
        seed_flag = _backends.spec(name).seed_flag
        if self._seed is not None and seed_flag:
            options.append(f"{seed_flag}{self._seed}")
        return tuple(options)

    def solve(self) -> Result:
        """Ask the bound backend whether a model exists.

        A model COUNTER is refused here rather than run. It would answer, and
        the answer would be a number -- which this method would then hand back
        as `Result(status="sat", model="1024")`, reading as "satisfiable, and
        here is the witness". That is a different claim from "there are 1024
        models", and a caller reading `.model` would never see the
        substitution. `.count()` is the method that asks a counter its own
        question.
        """
        name = self._require_backend()
        if _backends.spec(name).reads == "count":
            raise BackendNotFound(
                f"{name!r} is a model counter, not a solver: it reports how "
                f"many models exist, not whether one does. Call .count() "
                f"instead, or bind a solver with .to('z3')."
            )
        effective_args, mode = self._solver_options(name)
        used_options = self._effective_backend_options(name, effective_args)
        status, payload, seconds = _backends.run(
            name, self.script(), self._timeout, self._seed, self._path,
            effective_args)
        reason = payload if status == "unknown" else None
        if reason is not None and not reason.startswith(("timeout", "crash")):
            reason = None
        return Result(status=status, seconds=seconds, reason=reason,
                      model=payload if status == "sat" else None,
                      stdout=payload, backend_options=used_options,
                      semantic_mode=mode)

    def optimize(self) -> Result:
        """Solve, with the objectives the source declared.

        The same call as `.solve()` at the protocol level -- the objectives are
        already in the script, in the dialect the backend reads. The separate
        name is not sugar: it says which question was asked, which is what the
        fidelity floor is checked against.
        """
        name = self._require_backend()
        if _backends.spec(name).reads == "count":
            # `solve()` would refuse this too, but its message tells the caller
            # to use `.count()` -- which answers a different question from the
            # one `.optimize()` asked. Refuse here so the message names an
            # optimising backend as the thing that is missing.
            raise BackendNotFound(
                f"{name!r} is a model counter: it reports how many models "
                f"exist and has no notion of an objective. Bind an optimising "
                f"solver -- .to('z3') or .to('optimathsat')."
            )
        f = self.fidelity
        if not f.preserves_optimum:
            raise FidelityError(
                "this translation does not preserve the optimum "
                "(preserves_optimum is false), so an optimal value from it is "
                "not the source's optimum; "
                + self._bounds_text()
            )
        # `.script()` asks only `(check-sat)`, so a solver that found an
        # optimum never prints it. Asking is the difference between
        # `.optimize()` and `.solve()` at the protocol level after all -- the
        # docstring above used to claim they were the same call, and that was
        # how `.value()` came to return an empty string.
        # Only ask when there is something to ask about: on an objective-free
        # model an unconditional `(get-objectives)` turns `.model` from the
        # empty string into "(objectives\n)", which is a change in what
        # `.solve()` and `.optimize()` report for the same script.
        script = (self._objectives_script() if self.stats.num_objectives
                  else self.script())
        effective_args, mode = self._solver_options(name)
        used_options = self._effective_backend_options(name, effective_args)
        status, payload, seconds = _backends.run(
            name, script, self._timeout, self._seed, self._path, effective_args)
        reason = payload if status == "unknown" else None
        if reason is not None and not reason.startswith(("timeout", "crash")):
            reason = None
        return Result(status=status, seconds=seconds, reason=reason,
                      model=payload if status == "sat" else None,
                      objectives=_parse_objectives(payload) if status == "sat" else {},
                      stdout=payload, backend_options=used_options,
                      semantic_mode=mode)

    def _objectives_script(self) -> str:
        """`.script()`, with `(get-objectives)` asked after the check."""
        text = self.script()
        marker = "(check-sat)"
        at = text.rfind(marker)
        if at < 0:
            return text
        cut = at + len(marker)
        return text[:cut] + "\n(get-objectives)" + text[cut:]

    def value(self):
        """The single objective's value, or None. The `.item()` of this API.

        Raises when the model declares no objective, rather than returning
        None: "there is no objective" and "the objective has no value" are
        different answers, and a caller who cannot tell them apart will read
        the first as the second.
        """
        if self.stats.num_objectives == 0:
            raise FidelityError(
                "this model declares no objective, so it has no value; "
                ".solve() is the question it can answer"
            )
        r = self.optimize()
        if r.status != "sat" or not r.objectives:
            return None
        if len(r.objectives) > 1:
            raise FidelityError(
                f"this model has {len(r.objectives)} objectives, so 'the' "
                f"value is not defined; read Result.objectives from "
                f".optimize() instead"
            )
        return next(iter(r.objectives.values()))

    def count(self, *, scope: str = "source") -> Result:
        """How many models. Refuses when the translation did not preserve it.

        `scope="target"` means the unweighted, unprojected number of satisfying
        assignments to all declared Boolean variables in the supported
        propositional target formula. CNF auxiliaries have unique extensions,
        so counting all CNF variables yields this assignment count. This is not
        a count of arbitrary SMT structures or interpretations. The keyword
        distinguishes this target-level quantity from a source-model count.
        """
        if scope not in _COUNT_SCOPES:
            raise ValueError(
                f"scope must be one of {_COUNT_SCOPES!r}, not {scope!r}"
            )
        declared = self._declared_counting_extras()
        if declared:
            raise NotImplementedError(
                "this instance declares a " + " and ".join(sorted(declared))
                + " count, which this API does not compute -- it would return "
                "the plain unweighted, unprojected count, a number that "
                "answers a different question. The frontend reads and records "
                "those headers; nothing downstream applies them yet."
            )
        if scope == "source" and self.fidelity.count_status != "preserved":
            if self.fidelity.count_status == "unassessed":
                reason = "count preservation is unassessed"
            else:
                reason = "this translation provides no count-preservation guarantee"
            raise FidelityError(
                reason + "; counting the target is not established to count "
                "the source's models. " + self._bounds_text()
                + ". Pass scope='target' to count the target anyway."
            )
        name = self._require_backend()
        spec = _backends.spec(name)
        if spec.reads != "count":
            # The mirror of solve()'s refusal. A solver asked how many answers
            # whether, and `Result(status="sat", count=None)` is
            # indistinguishable from a counter that failed to report one.
            raise BackendNotFound(
                f"{name!r} is a solver, not a model counter: it reports "
                f"whether a model exists, not how many. Bind a counter with "
                f".to('d4')."
            )
        text = self.cnf()
        status, payload, seconds = _backends.run(
            name, text, self._timeout, self._seed, self._path, self._args)
        count = int(payload) if status == "sat" and payload.isdigit() else None
        return Result(status=status, seconds=seconds,
                      reason=payload if status == "unknown" else None,
                      count=count, stdout=payload)

    #: EncodingChoice strategies that make the counting question a different
    #: one from the plain model count.
    _COUNTING_EXTRAS = {"counting-weights": "weighted",
                        "counting-projection": "projected"}

    def _declared_counting_extras(self) -> set:
        """Which of the source's counting modifiers this formula carries."""
        if self._t is None:
            return set()
        return {self._COUNTING_EXTRAS[c.strategy]
                for c in self._t.report.choices
                if c.strategy in self._COUNTING_EXTRAS}

    def _bounds_text(self) -> str:
        bounds = list(self.fidelity.bounds)
        if not bounds:
            return "no bound was recorded"
        parts = [f"{b.kind.name}={b.value} at {b.site}" for b in bounds]
        return "bounds: " + "; ".join(parts)

    def cnf(self) -> str:
        """The formula as DIMACS CNF, via Tseitin.

        Counting backends read DIMACS, not SMT-LIB, so `.count()` needs this
        and `.solve()` does not. Tseitin rather than distribution because the
        distributive normal form is exponential -- and because Tseitin's
        two-sided gate clauses make every auxiliary functionally determined,
        so counting over all DIMACS variables counts the satisfying Boolean
        assignments of the supported propositional target formula without
        projection. This says nothing about the number of source-level models
        or arbitrary SMT structures.

        Refuses a formula with a non-Boolean variable, by name and sort: a
        counter over DIMACS has no theories, and bit-blasting is a translation
        this does not do. Silently dropping the theory part would produce a
        number that answers a different question, which is the failure mode
        this tree is organised against.
        """
        p = self._require_translation().parser

        # getVariables() contains declared variables and Tseitin temporaries,
        # but the parser stores function symbols separately. An unused
        # uninterpreted function has no application for cnf_atoms() to notice;
        # omitting it would silently change target-model cardinality. The raw
        # SMT parser and HIR translation retain deterministic func_def bodies.
        # Their Boolean applications are expanded in the isolated parser below;
        # free and recursive function interpretations still require refusal.
        unsupported_functions = [f for f in p.functions if not f.is_func_def]
        if unsupported_functions:
            shown = ", ".join(
                f"{f.name} ({f.kind})" for f in unsupported_functions[:5])
            raise NotImplementedError(
                f"cannot emit DIMACS: {len(unsupported_functions)} function "
                f"declaration or recursive definition(s) have interpretations "
                f"that the Boolean assignment encoding cannot count ({shown})."
            )

        # Free uninterpreted sort constructors describe arbitrary carriers and
        # are not Boolean assignments. Reject every such declaration present
        # in the translated parser before either assertion path. HIR retains
        # explicit constructor declarations, including unused ones, so this
        # check covers the complete declared free-sort vocabulary.
        uninterpreted_sorts = list(p.uninterpreted_sorts)
        if uninterpreted_sorts:
            shown = ", ".join(uninterpreted_sorts[:5])
            raise NotImplementedError(
                f"cannot emit DIMACS: {len(uninterpreted_sorts)} uninterpreted "
                f"sort declaration(s) have arbitrary carrier interpretations "
                f"that the Boolean assignment encoding cannot represent "
                f"({shown})."
            )

        asserts = list(p.assertions)

        non_bool = [(v.name, str(v.sort)) for v in p.variables
                    if not _is_bool_sort(v.sort)]
        if non_bool:
            shown = ", ".join(f"{n}:{s}" for n, s in non_bool[:5])
            raise NotImplementedError(
                f"cannot emit DIMACS: {len(non_bool)} variable(s) are not "
                f"Boolean ({shown}). A DIMACS counter has no theories, and "
                f"bit-blasting is a translation this does not do."
            )

        if any(v.is_temp_var for v in p.variables):
            raise NotImplementedError(
                "cannot emit DIMACS: the source parser already contains "
                "internal temporary variables outside its declared Boolean "
                "vocabulary"
            )

        if not asserts:
            # Still every DECLARED variable, and this is not a nicety: a file
            # with a vocabulary and no clauses has 2**n models, not one. The
            # DIMACS frontend states the same invariant on the way in -- "the
            # file's vocabulary is the HEADER's, not the clauses'" -- and
            # returning "p cnf 0 0" here threw it away on the way out. Found by
            # a randomised differential test (see
            # test_cnf_preserves_the_count_over_random_formulas): 300 small
            # CNFs, and every single mismatch was this one shape.
            return f"p cnf {len(p.declared_variables)} 0\n"

        # Detected before the attempt rather than diagnosed after it. The
        # engine's own exception for this case says only "parse error" -- its
        # detail goes to stderr -- so a handler that relabelled it "a
        # quantifier" would be guessing, and would say the same thing about an
        # internal error. Finding the quantifier ourselves means the refusal
        # names what is actually there.
        quantified = [n for assertion in asserts for n in _subterms(assertion)
                      if n.kind in ("forall", "exists")]
        if quantified:
            raise NotImplementedError(
                f"cannot emit DIMACS: the formula contains a "
                f"{quantified[0].kind} quantifier. DIMACS is quantifier-free "
                f"propositional logic; a QBF instance is a different format "
                f"and a different question."
            )

        # Tseitin conversion registers auxiliary variables in Parser state.
        # Formula objects and their .to() siblings share this parser, so doing
        # the conversion here makes later calls count stale, unconstrained
        # auxiliaries. Reparse the canonical accepted Boolean script into a
        # fresh Parser and perform every stateful CNF operation there.
        from . import Parser
        try:
            cnf_parser = Parser()
            cnf_parser.set_option("expand_functions", True)
            cnf_parser.parse_string(p.dump_smt2())
        except Exception as error:
            raise NotImplementedError(
                f"cannot emit DIMACS: the accepted Boolean formula could not "
                f"be isolated for CNF conversion: {error}"
            ) from None

        # Refuse if canonical serialization did not retain the assertion and
        # variable vocabulary. This includes unused declared Bool variables,
        # whose assignments are part of the target Boolean assignment count.
        source_variables = [(v.name, str(v.sort)) for v in p.declared_variables]
        cnf_variables = [(v.name, str(v.sort)) for v in cnf_parser.variables]
        if (source_variables != cnf_variables
                or len(cnf_parser.assertions) != len(asserts)):
            raise NotImplementedError(
                "cannot emit DIMACS: canonical SMT-LIB serialization changed "
                "the assertion count or declared variable vocabulary"
            )
        cnf_asserts = list(cnf_parser.assertions)
        top = cnf_parser.and_(cnf_asserts) if len(cnf_asserts) > 1 else cnf_asserts[0]

        try:
            root, clauses = cnf_parser.to_tseitin_cnf(top)
        except Exception as error:
            # Whatever else went wrong, reported as the engine described it.
            raise NotImplementedError(
                f"cannot emit DIMACS: the engine could not put this formula "
                f"into CNF: {error}"
            ) from None

        # A Bool-sorted uninterpreted application -- `(q a)` for
        # `(declare-fun q (Bool) Bool)` -- is not a VARIABLE, so the sort check
        # above never sees it. `to_tseitin_cnf` replaces each such atom with a
        # fresh abstraction variable and emits NO clause linking the two, which
        # is correct for a solver that will refine the abstraction and silently
        # wrong for a counter: the emitted file counts models of the Boolean
        # skeleton, not of the formula. `cnf_atoms()` is populated exactly when
        # that happened, so it is the general guard -- it catches any theory
        # atom, not only the UF case that exposed it.
        abstracted = cnf_parser.cnf_atoms()
        if abstracted:
            shown = ", ".join(cnf_parser.to_string(a) for a in abstracted[:5])
            raise NotImplementedError(
                f"cannot emit DIMACS: {len(abstracted)} atom(s) were replaced "
                f"by Boolean abstractions with no defining clause ({shown}). "
                f"Counting the result would count the abstraction, not the "
                f"formula."
            )

        # `variables` walks the declared table AND the temp table `mkTempVar`
        # writes into, so this is every variable the CNF mentions.
        index = {v.name: i + 1 for i, v in enumerate(cnf_parser.variables)}
        rows = []
        for node in [*clauses, root]:
            lits = _clause_literals(node, index)
            if lits is None:        # a tautology; contributes nothing
                continue
            rows.append(lits)
        head = f"p cnf {len(index)} {len(rows)}\n"
        body = "".join(" ".join(str(l) for l in row) + " 0\n" for row in rows)
        return head + body
