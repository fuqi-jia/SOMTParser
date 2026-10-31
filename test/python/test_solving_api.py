"""The solving API: binding a formula to a backend, and what comes back.

`.to()` follows PyTorch's type semantics -- it returns the SAME type with a
different binding, does no work, and does not mutate the original. That is
worth testing rather than assuming, because an implementation that mutated in
place would pass every single-use example and fail the moment a caller bound
one formula to two backends.

The error taxonomy is the other half, and it is a batch-layer requirement: a
timeout is a legitimate experimental outcome and must be DATA, or one slow
instance breaks a loop over 284 files. A missing solver and a fidelity
violation are exceptions, because continuing past either produces a number
that means something other than what it says.
"""

import pytest
import subprocess

import somtparser as sp
from somtparser import _backends


PLAIN = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))"


def test_backend_rejection_preserves_stdout_diagnostic(monkeypatch):
    def rejected(*args, **kwargs):
        return subprocess.CompletedProcess(args[0], 1,
            stdout='(error "unknown constant set.card")\n', stderr='')
    monkeypatch.setattr(_backends.subprocess, 'run', rejected)
    status, reason, _ = _backends.run('z3', '(check-sat)', 1, None, '/unused/z3')
    assert status == 'unknown'
    assert 'exit 1' in reason and 'unknown constant set.card' in reason


def _read():
    return sp.read(source=PLAIN, language="smtlib2")


@pytest.fixture
def uninstalled(monkeypatch):
    """A registered backend whose binary can never exist.

    `.to()` validates names eagerly, so testing the missing-BINARY path needs a
    name the registry accepts and a binary the machine does not have. Which real
    solvers are installed is a fact about the machine, so picking a real one would
    make this test pass or skip depending on where it runs. Injecting the fixture
    here rather than shipping it in `BACKENDS` keeps the registry honest about what
    this build can actually run.
    """
    name = "definitely-not-installed"
    spec = _backends.BackendSpec(
        name=name, binary=name, dialect="Z3",
        install_hint="this is a test fixture, not a real solver",
    )
    monkeypatch.setitem(_backends.BACKENDS, name, spec)
    return name


def test_read_returns_a_formula_with_cheap_properties():
    f = _read()
    assert f.language == "smtlib2"
    assert f.fidelity.sound
    assert f.backend is None
    # Properties are cheap and repeatable; nothing has been solved.
    assert f.fidelity is f.fidelity


def test_to_does_not_mutate_and_returns_the_same_type():
    f = _read()
    g = f.to("z3")
    assert isinstance(g, type(f))
    assert g is not f
    assert f.backend is None          # the original is untouched
    assert g.backend == "z3"


def test_to_is_lazy(uninstalled):
    # Binding a backend that does not exist must not raise: nothing has run.
    # The failure belongs to .solve(), where the work is.
    f = _read().to(uninstalled)
    assert f.backend == uninstalled


def test_missing_backend_raises_naming_the_binary(uninstalled):
    f = _read().to(uninstalled)
    with pytest.raises(sp.BackendNotFound) as excinfo:
        f.solve()
    assert uninstalled in str(excinfo.value)


def test_unknown_backend_name_is_refused_by_name():
    with pytest.raises(sp.BackendNotFound) as excinfo:
        _read().to("frobnicate")
    assert "frobnicate" in str(excinfo.value)


def test_repr_names_what_identifies_the_formula():
    f = _read()
    text = repr(f)
    assert "smtlib2" in text
    assert "fidelity" in text
    assert "Formula(" in text


def test_backend_selects_the_dialect():
    # Binding the backend is what makes a dialect mismatch unrepresentable:
    # before this, a caller could render OptiMathSAT syntax and feed it to z3.
    # Two objectives AND an explicit combination. Both halves are load-bearing:
    # a single objective prints identically in both dialects, which would make
    # this test vacuous, and two objectives without `:opt.priority` are refused
    # outright -- the frontend will not let silence choose lexicographic, since
    # Z3 documents that as its default and a reader would never see the choice
    # being made (src/lowering/omt_emitter.cpp:100-104 argues the same for the
    # emitting side).
    source = ("(set-logic QF_LIA)(set-option :opt.priority lex)"
              "(declare-const x Int)(declare-const y Int)"
              "(assert (> x 0))(assert (> y 0))(minimize x)(minimize y)")
    z3_text = sp.read(source=source, language="smtlib2").to("z3").script()
    smtlib_text = sp.read(source=source, language="smtlib2").to("smtlib").script()
    assert "opt.priority" in z3_text
    assert "define-multi-objective" in smtlib_text


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_solve_returns_sat_and_a_model():
    r = _read().to("z3").solve()
    assert r.status == "sat"
    assert r.seconds >= 0.0


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_unsat_is_a_status_not_an_exception():
    f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)"
                       "(assert (> x 0))(assert (< x 0))",
                language="smtlib2")
    assert f.to("z3").solve().status == "unsat"


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_timeout_is_data_not_an_exception():
    # A batch over 284 files must not stop because one was slow.
    f = _read().to("z3", timeout=0.001)
    r = f.solve()
    assert r.status in ("sat", "unknown")
    if r.status == "unknown":
        assert r.reason == "timeout"


def test_a_failure_is_reported_by_its_error_not_its_first_note():
    """`TranslationError` must carry the ERROR, not whatever came first.

    A frontend may say things before it fails. Essence' notes that it skipped
    a `branching` search directive -- a solver hint with no semantic content,
    correctly skipped -- and then fails several lines later on a construct it
    cannot parse. Taking `diagnostics[0]` reported the NOTE's code and text as
    the cause.

    That is the code a corpus sweep buckets failures by, so the mistake filed
    genuine parse gaps under `E_UNSUPPORTED_CONSTRUCT` and made the
    failure-cause distribution wrong for every file whose frontend speaks
    before it fails -- the one output a corpus exists to produce. The C++
    `Diagnostics::firstErrorCode()` had it right all along; only this wrapper
    ignored severity.

    The model is INLINE and not a corpus file, which is the second lesson
    here rather than a style choice. This test was written against
    `autogen_gen14_1.eprime`, then repointed at
    `basic_comprehension_letting.eprime` when comprehension guards made the
    first one translate -- and within the hour `allDiff` over a list, `/`, `%`
    and `min`/`max` made the second one translate too. A test that pins "a file
    that fails" is coupled to coverage progress, so every gap closed is a test
    invalidated, and the failure arrives as a puzzle rather than as a finding.

    An inline model fixes the two things the assertion actually needs and
    nothing else: a NOTE emitted before the failure (`branching`, which this
    frontend skips with a note because a search directive constrains nothing),
    and an ERROR carrying a DIFFERENT code (`E_TYPE` for the undeclared name).
    The codes must differ or the assertion cannot discriminate: the note's own
    code is `E_UNSUPPORTED_CONSTRUCT`, so grading against that would pass
    whether or not the wrapper respected severity.
    """
    with pytest.raises(sp.TranslationError) as excinfo:
        sp.read(source="language ESSENCE' 1.0\n"
                       "find x: int(1..3)\n"
                       "branching on [x]\n"
                       "such that x = no_such_name\n",
                language="essence", profile="ground")
    error = excinfo.value
    # The note comes first and must NOT be what is reported.
    assert error.diagnostics[0].severity == sp.Severity.NOTE
    assert "branching" in error.diagnostics[0].message
    assert error.code == sp.ErrorCode.E_TYPE
    assert "branching" not in str(error)
