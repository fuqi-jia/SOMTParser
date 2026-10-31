"""The batch layer: sweeping a corpus, scoped defaults, reproducible seeds.

Thin by design -- it is the same core with defaults applied, because a batch
run and an interactive one must not be able to disagree about what a profile
means. The one thing it adds that the core cannot have is that a file which
fails to translate is YIELDED rather than raised: a sweep over 284 files that
stops at the first refusal measures nothing.
"""

import glob

import pytest

import somtparser as sp


def test_profile_scopes_a_default():
    with sp.profile("bv32"):
        f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                    language="smtlib2")
        assert f.fidelity.count_status == "no_guarantee"
    # ...and the scope ends with the block.
    g = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                language="smtlib2")
    assert g.fidelity.count_status == "unassessed"


def test_profile_nests():
    with sp.profile("bv32"):
        with sp.profile("default"):
            f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                        language="smtlib2")
            assert f.fidelity.count_status == "unassessed"


def test_sweep_yields_one_formula_per_matching_file():
    pattern = "languages/dimacs/instances/ok/*"
    found = list(sp.sweep(pattern))
    assert len(found) == len(glob.glob(pattern))
    assert len(found) >= 3, "the ok corpus should not have shrunk to nothing"
    # Every file in ok/ translates, so every item answers .fidelity and none
    # carries an error. Naming both halves is what makes this discriminate: an
    # implementation that yielded an empty Formula for everything would pass a
    # test that only counted items.
    for f in found:
        assert f.error is None, f"{f!r} carries an error"
        assert f.fidelity.sound


def test_sweep_yields_failures_instead_of_raising():
    # A sweep that stopped at the first refusal would measure nothing.
    pattern = "languages/dimacs/instances/reject/*"
    found = list(sp.sweep(pattern))
    assert len(found) == len(glob.glob(pattern))
    assert found, "the reject directory should not be empty"
    # ALL of them, not `any` -- `any` passes when one file happens to fail and
    # the rest are silently swallowed.
    assert all(f.error is not None for f in found)
    assert all(isinstance(f.error, sp.TranslationError) for f in found)


def test_a_failed_formula_says_so_rather_than_dying_obscurely():
    found = [f for f in sp.sweep("languages/dimacs/instances/reject/*")
             if f.error is not None]
    assert found
    f = found[0]
    assert "FAILED" in repr(f)          # printable, which is how you inspect a sweep
    with pytest.raises(sp.TranslationError) as excinfo:
        f.fidelity
    assert "did not translate" in str(excinfo.value)


def test_seed_is_recorded_on_the_formula():
    sp.seed(1234)
    try:
        f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                    language="smtlib2").to("z3")
        assert f.seed == 1234
    finally:
        sp.seed(None)


def test_sweep_resolves_the_scope_at_the_call_not_at_iteration():
    """A stored sweep keeps the profile the block it was created in asked for.

    `sweep` returns a generator, and a generator FUNCTION would not run a line
    of its body until first iteration -- so the scoped-default lookup would
    happen wherever the caller happened to iterate, not where they wrote the
    `with`. Building the generators first and consuming them later is an
    ordinary thing to write, and the failure is silent: provenance would
    honestly record `default`, because `default` is what ran.
    """
    pattern = "languages/dimacs/instances/ok/simple.cnf"
    with sp.profile("bv32"):
        stored = sp.sweep(pattern)          # not iterated inside the block
    got = [f.translation.report.provenance.profile_id for f in stored]
    assert got == ["bv32"]

    # ...and the ambient default still applies when there is no block.
    plain = [f.translation.report.provenance.profile_id
             for f in sp.sweep(pattern)]
    assert plain == ["default"]


def test_sweep_captures_the_seed_at_the_call_too():
    pattern = "languages/dimacs/instances/ok/simple.cnf"
    sp.seed(1234)
    try:
        stored = sp.sweep(pattern)
    finally:
        sp.seed(None)                        # cleared BEFORE iteration
    assert [f.seed for f in stored] == [1234]


def test_the_seed_reaches_the_solver_argv():
    """`.seed` being stored on the Formula is not the claim worth pinning.

    The claim is that a seeded run is reproducible, which requires the value
    to arrive in the process's argv. A `solve()` that dropped `self._seed` on
    the way to `_backends.run` would leave `f.seed == 1234` true and every
    run unseeded -- so asserting the attribute proves nothing about the thing
    the feature exists for. Captured here without needing a solver installed.
    """
    from somtparser import _backends

    captured = {}

    def fake_run(argv, **kwargs):
        captured["argv"] = list(argv)

        class Done:
            returncode = 0
            stdout = "sat\n"
            stderr = ""
        return Done()

    real = _backends.subprocess.run
    _backends.subprocess.run = fake_run
    try:
        sp.seed(4242)
        try:
            f = sp.read(source="p cnf 2 1\n1 2 0\n", language="dimacs")
            f.to("z3", path="/nonexistent/z3").solve()
        finally:
            sp.seed(None)
    finally:
        _backends.subprocess.run = real

    assert any("4242" in a for a in captured["argv"]), captured["argv"]
    assert any(a.startswith("smt.random_seed=") for a in captured["argv"]), \
        captured["argv"]


def test_sweep_created_outside_a_block_is_not_captured_by_one():
    """The mirror of the case above, and the one the first fix missed.

    `sweep` resolved its profile to `None` when no block was in effect, and
    `read` treats `None` as "not given" and consults the thread-local -- at
    iteration time. So a sweep created outside any block and iterated inside
    one silently picked the block up, which is the same bug in the other
    direction. Resolving to the concrete string `"default"` closes it.
    """
    pattern = "languages/dimacs/instances/ok/simple.cnf"
    lazy = sp.sweep(pattern)                 # no scope in effect here
    with sp.profile("bv32"):
        got = [f.translation.report.provenance.profile_id for f in lazy]
    assert got == ["default"]
