"""`.count()`, and the refusal that makes the number mean something.

A translation can preserve satisfiability perfectly and still change how many
models there are, so a count is only meaningful when the fidelity record says
the translation preserved it. When it did not, `.count()` raises rather than
returning a number nobody can qualify -- which is this project's own rule: a
refusal names the construct, and a number that silently means something else
is the failure mode the whole tree is organised against.

`.count()` hands a counting backend DIMACS, not SMT-LIB -- d4 and ganak read
DIMACS from a file, not SMT-LIB from stdin. `.cnf()` is the emitter behind
that, and it is tested here as TEXT, so the tests that pin its correctness run
with no solver installed at all.
"""

import itertools

import pytest

import somtparser as sp


def _counting_formula():
    return sp.read(source="p cnf 2 1\n1 2 0\n", language="dimacs")


def _bounded_formula():
    # `bv32` bounds an unbounded Int, which turns infinitely many models into
    # finitely many -- an under-approximation, and not count-preserving.
    return sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                   language="smtlib2", profile="bv32")


def test_a_plain_translation_leaves_count_unassessed():
    f = _counting_formula().fidelity
    assert f.count_status == "unassessed"
    assert not f.preserves_count


def test_a_bounded_translation_does_not():
    assert _bounded_formula().fidelity.count_status == "no_guarantee"


def test_count_refuses_when_the_count_was_not_preserved():
    f = _bounded_formula().to("d4")
    with pytest.raises(sp.FidelityError) as excinfo:
        f.count()
    message = str(excinfo.value)
    assert "no count-preservation guarantee" in message
    # The refusal names the bound that destroyed it, so a reader knows which
    # knob produced the number they cannot have.
    assert "BV_WIDTH" in message or "bound" in message.lower()


def test_scope_target_passes_the_gate_that_scope_source_fails():
    # Knowingly asking for the target's count is legitimate; silently getting
    # it is not, and the keyword is the whole difference. What this pins is
    # the GATE, not a number.
    #
    # No formula in this tree can currently reach a counter with
    # `scope="target"`, and the reason is structural rather than an
    # environment accident: `.cnf()` emits DIMACS only for Boolean-only
    # formulas, and every construct that clears `preserves_count` -- a bounded
    # Int, an OPB/WBO relaxation whose variables lift to 0/1 Ints -- leaves a
    # non-Boolean variable behind. So "count is not preserved" and "can be
    # written as DIMACS" are, today, disjoint.
    #
    # That makes the reachable question "did `scope='target'` get PAST the
    # fidelity gate", and it is answerable exactly: `scope="source"` must
    # raise FidelityError, and `scope="target"` must raise something that is
    # NOT a FidelityError. An implementation that ignored the keyword would
    # raise FidelityError both times and fail here.
    f = _bounded_formula().to("d4")
    with pytest.raises(sp.FidelityError):
        f.count(scope="source")
    with pytest.raises(Exception) as excinfo:
        f.count(scope="target")
    assert not isinstance(excinfo.value, sp.FidelityError), (
        "scope='target' must bypass the fidelity gate, not trip it"
    )
    # And it failed for the honest downstream reason, named.
    assert isinstance(excinfo.value, (NotImplementedError, sp.BackendNotFound))


def test_count_rejects_an_unknown_scope():
    with pytest.raises(ValueError):
        _counting_formula().to("d4").count(scope="sideways")


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_optimize_returns_the_objective_value():
    f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)"
                       "(assert (>= x 3))(minimize x)",
                language="smtlib2")
    r = f.to("z3").optimize()
    assert r.status == "sat"


def test_source_count_refuses_an_unassessed_translation():
    with pytest.raises(sp.FidelityError) as excinfo:
        _counting_formula().to("d4").count()
    assert "unassessed" in str(excinfo.value)


@pytest.mark.skipif(sp.backend_path("d4") is None, reason="d4 unavailable")
def test_target_count_is_explicit_even_when_source_count_is_unassessed():
    r = _counting_formula().to("d4").count(scope="target")
    assert r.count == 3          # (1∨2) over two variables: TT TF FT


# -- .cnf(): the DIMACS emitter, verified as text with no solver installed --


def _models_of_dimacs(text):
    """Brute-force model count of a DIMACS string, over all its variables."""
    header = [l for l in text.splitlines() if l.startswith("p cnf")][0]
    n = int(header.split()[2])
    clauses = [[int(t) for t in l.split()[:-1]]
               for l in text.splitlines()
               if l and not l.startswith(("p", "c"))]
    total = 0
    for bits in itertools.product([False, True], repeat=n):
        def holds(lit):
            return bits[abs(lit) - 1] if lit > 0 else not bits[abs(lit) - 1]
        if all(any(holds(l) for l in c) for c in clauses):
            total += 1
    return total


def test_cnf_emits_a_wellformed_header():
    text = _counting_formula().cnf()
    header = [l for l in text.splitlines() if l.startswith("p cnf")]
    assert len(header) == 1
    n, m = int(header[0].split()[2]), int(header[0].split()[3])
    body = [l for l in text.splitlines() if l and not l.startswith(("p", "c"))]
    assert len(body) == m            # the header counts the clauses it has
    assert all(l.endswith(" 0") for l in body)
    assert all(1 <= abs(int(t)) <= n for l in body for t in l.split()[:-1])


def test_the_emitted_cnf_counts_target_boolean_assignments():
    # Tseitin's auxiliaries are functionally determined, so counting every
    # DIMACS variable counts the supported propositional target assignments
    # rather than merely preserving satisfiability.
    # `(x1 ∨ x2)` over two variables has 3 models. Counted here over EVERY
    # variable the CNF mentions, auxiliaries included -- if a future change
    # made a gate one-sided, this number would grow and this test would fail,
    # which an assertion that `preserves_count is True` could never do.
    assert _models_of_dimacs(_counting_formula().cnf()) == 3


def test_cnf_refuses_a_theory_formula_by_name_and_sort():
    f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))",
                language="smtlib2")
    with pytest.raises(NotImplementedError) as excinfo:
        f.cnf()
    message = str(excinfo.value)
    assert "x" in message and "Int" in message


def test_parser_reports_uninterpreted_sort_declarations():
    p = sp.Parser().parse_string(
        "(set-logic QF_UF)(declare-sort U 0)(declare-sort Box 1)"
    )
    assert p.uninterpreted_sorts == ["U", "Box"]


def test_cnf_refuses_unused_uninterpreted_sort_without_assertions():
    # Even an unused sort introduces arbitrary carrier interpretations; the
    # empty-CNF fast path must not report the Boolean assignment count instead.
    f = sp.read(source="(set-logic QF_UF)(declare-sort U 0)",
                language="smtlib2")
    with pytest.raises(NotImplementedError, match="uninterpreted sort"):
        f.cnf()


def test_cnf_refuses_unused_uninterpreted_sort_with_assertions():
    # The same vocabulary restriction applies before the ordinary assertion
    # conversion path, even if the declared carrier is absent from the formula.
    f = sp.read(source="(set-logic QF_UF)(declare-sort U 0)"
                       "(declare-const b Bool)(assert b)",
                language="smtlib2")
    with pytest.raises(NotImplementedError, match="uninterpreted sort"):
        f.cnf()


def test_solve_refuses_a_counter_rather_than_mislabelling_its_answer():
    # A counter answers `.solve()` with a number. Returned as
    # `Result(status="sat", model="1024")` it reads as "satisfiable, and here
    # is the witness" -- a different claim from "there are 1024 models", and
    # one a caller reading `.model` could never tell apart. So `.solve()`
    # refuses, and says which method does ask a counter its own question.
    f = _counting_formula().to("d4")
    with pytest.raises(sp.BackendNotFound) as excinfo:
        f.solve()
    message = str(excinfo.value)
    assert "counter" in message
    assert ".count()" in message


def test_a_counters_trailing_statistics_do_not_become_the_count():
    # Every one of these tools prints timing and memory AFTER its answer, so a
    # backwards scan for the last numeric line can return a decision count or
    # a millisecond total instead of the count. A wrong count is far worse
    # than a refused one: nothing downstream can tell it from a right one.
    #
    # The BARE trailing number is what makes this discriminate, and it is here
    # on purpose. A breakage probe that restored the backwards scan left this
    # test passing when the trailing lines were all `c o …`-prefixed -- the
    # prefix alone defeats `isdigit()`, so the old code got that case right by
    # accident and the test proved nothing. The input below fails a backwards
    # scan (it would answer 131) and passes a forwards scan that prefers a
    # marked line.
    from somtparser import _backends
    stdout = ("c o solving...\n"
              "s 1024\n"
              "c o decisions 77\n"
              "131\n")
    assert _backends._count_status(stdout) == ("sat", "1024")


def test_the_model_counting_competition_answer_line_is_read():
    from somtparser import _backends
    assert _backends._count_status(
        "c s type mc\nc s exact arb int 42\n") == ("sat", "42")


def test_a_bare_number_is_a_count_only_when_nothing_is_marked():
    from somtparser import _backends
    # First bare line wins, not last -- the trailing line is statistics.
    assert _backends._count_status("8\n999\n") == ("sat", "8")
    assert _backends._count_status("no answer here\n")[0] == "unknown"


def test_a_name_that_is_not_executable_is_not_a_backend_path(tmp_path, monkeypatch):
    # `os.path.exists` is satisfied by a directory of the right name, which
    # subprocess.run then rejects with IsADirectoryError -- escaping the
    # contract that says a missing binary is reported as one specific,
    # explaining exception.
    from somtparser import _backends
    (tmp_path / "d4").mkdir()
    monkeypatch.setattr(_backends.sys, "executable", str(tmp_path / "python"))
    monkeypatch.setattr(_backends.shutil, "which", lambda _: None)
    assert _backends.backend_path("d4") is None


def test_rebinding_keeps_a_timeout_the_caller_set():
    # torch's `.to()` is cumulative across its arguments; dropping a limit on
    # re-bind would turn an instance that reports `unknown` into one that
    # hangs a batch.
    f = _counting_formula().to("z3", timeout=5).to("cvc5")
    assert f._timeout == 5
    assert f.backend == "cvc5"
    # ...and an explicit value still overrides.
    assert f.to("z3", timeout=1)._timeout == 1


def test_language_reports_what_detection_chose():
    # A sweep groups its results by this field, so "auto" for every detected
    # file loses exactly the distinction the field exists to record.
    f = sp.read("languages/opb/instances/ok/wbo_binding.wbo")
    assert f.language == "opb"


def test_a_vocabulary_with_no_clauses_still_has_2n_models():
    # `p cnf 2 0` declares two variables and constrains neither, so it has 4
    # models, not 1. The DIMACS frontend states the invariant on the way in --
    # the file's vocabulary is the HEADER's, not the clauses' -- and `.cnf()`
    # threw it away on the way out, emitting `p cnf 0 0`. A counter reads that
    # as exactly one model.
    #
    # None of the nine hand-written cases tried before this one caught it;
    # the randomised test below did, on the first run.
    text = sp.read(source="p cnf 2 0\n", language="dimacs").cnf()
    assert text.splitlines()[0] == "p cnf 2 0"
    assert _models_of_dimacs(text) == 4


def test_cnf_preserves_the_count_over_random_formulas():
    """The property, sampled rather than exemplified.

    Enumerate the models of a random small CNF directly, enumerate the models
    of what `.cnf()` emits for it over EVERY variable the emitted file
    declares, and require the two to be equal. This checks that the supported
    propositional target representation and its emitted DIMACS have the same
    unweighted, unprojected Boolean assignment count. It does not establish
    source-count fidelity for arbitrary translations, and an example test
    cannot falsify the encoder property -- it can only confirm the shapes
    someone thought to write down.

    Seeded, so a failure is reproducible and a green run is not luck.
    """
    import itertools
    import random

    rng = random.Random(20260921)
    for _ in range(120):
        nvars = rng.randint(1, 4)
        clauses = [
            [rng.choice([1, -1]) * rng.randint(1, nvars)
             for _ in range(rng.randint(1, 3))]
            for _ in range(rng.randint(0, 4))
        ]
        source = (f"p cnf {nvars} {len(clauses)}\n"
                  + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses))

        expected = 0
        for bits in itertools.product([False, True], repeat=nvars):
            def holds(lit):
                return bits[abs(lit) - 1] if lit > 0 else not bits[abs(lit) - 1]
            if all(any(holds(l) for l in c) for c in clauses):
                expected += 1

        emitted = sp.read(source=source, language="dimacs").cnf()
        assert _models_of_dimacs(emitted) == expected, (
            f"count changed for:\n{source}\nemitted:\n{emitted}"
        )


def test_optimize_refuses_a_counter_and_says_what_to_bind():
    # `solve()` refuses a counter too, but its message says to call `.count()`
    # -- which answers a different question from the one `.optimize()` asked.
    # Pinned separately because a refactor that had optimize() reach the
    # backend directly rather than through solve() would silently drop the
    # refusal and nothing else would notice.
    f = _counting_formula().to("d4")
    with pytest.raises(sp.BackendNotFound) as excinfo:
        f.optimize()
    message = str(excinfo.value)
    assert "objective" in message, (
        "the refusal must name what a counter lacks for THIS question; "
        "falling through to solve()'s message would say 'call .count()', "
        "which is not what the caller asked for"
    )
    assert ".count()" not in message


# --- the count a fidelity flag is ASSERTING, measured -----------------------

def _sexp(text):
    """Parse s-expressions, keeping |quoted| symbols whole."""
    import re
    toks = re.findall(r"\|[^|]*\||\(|\)|[^\s()]+", text)

    def parse(i):
        out = []
        while i < len(toks):
            t = toks[i]
            if t == "(":
                sub, i = parse(i + 1)
                out.append(sub)
            elif t == ")":
                return out, i + 1
            else:
                out.append(t)
                i += 1
        return out, i

    return parse(0)[0]


def _int_value(node):
    """An SMT-LIB Int value: `3`, or `(- 3)` for a negative one.

    Worth its own function because getting this wrong is silent: a parser that
    mangles `(- 1)` produces a malformed blocking clause, the next check-sat
    comes back unsat, and the enumeration stops early reporting a count that
    looks plausible. That happened while this test was being written.
    """
    if isinstance(node, list):
        assert node[0] == "-", node
        return f"(- {node[1]})", -int(node[1])
    return node, int(node)


def _enumerate(body, names, z3_path, limit=500):
    """How many distinct assignments to @p names satisfy @p body."""
    import subprocess
    blocked, seen = [], 0
    while seen < limit:
        script = (body + "\n".join(blocked) + "\n(check-sat)\n(get-value ("
                  + " ".join(names) + "))\n")
        out = subprocess.run([z3_path, "-in"], input=script, text=True,
                             capture_output=True).stdout
        if not out.startswith("sat"):
            break
        pairs = [(p[0],) + _int_value(p[1])
                 for p in _sexp(out.split("\n", 1)[1])[0]]
        assert len(pairs) == len(names), (len(pairs), len(names))
        blocked.append("(assert (not (and " + " ".join(
            f"(= {k} {lit})" for k, lit, _ in pairs) + ")))")
        seen += 1
    return seen


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_the_xcsp3_circuit_encoding_really_does_multiply_the_count():
    """`preserves_count = False` on the circuit encoding is a measurement.

    The flag says the encoding does not preserve the model count. A C++ test
    asserts the flag; this one asserts the fact the flag is about, by counting
    both sides. Without it, someone who later pins the rotation -- forcing one
    active node to position 0 would do it -- has no way to learn that the flag
    could go back to `exact()`, and someone who breaks the encoding further has
    no way to learn the flag is now too weak rather than too strong.

    The position witnesses are constrained only by implications, all of which
    are invariant under rotating the positions along the cycle. So one
    assignment to the successors extends to `actual_size` target models.
    """
    import re

    # Three nodes, inline rather than from `instances/ok/circuit.xml`: that
    # fixture has four, and the expected counts below are derived from the
    # cycle structure of a specific size. A test whose numbers depend on a
    # fixture someone may extend is a test that will one day fail for a reason
    # that has nothing to do with what it is checking.
    instance = ('<instance format="XCSP3" type="CSP">'
                '<variables><array id="x" size="[3]"> 0..2 </array></variables>'
                '<constraints><circuit><list>x[]</list></circuit></constraints>'
                '</instance>')
    raw = sp.read(source=instance, language="xcsp3").script()
    body = raw.replace("(check-sat)\n(exit)\n", "")
    names = re.findall(r"\(declare-fun (\S+) \(\) Int\)", raw)
    successors = [n for n in names if not n.startswith("__somt")]
    assert successors and len(names) > len(successors), names

    z3 = sp.backend_path("z3")
    source_models = _enumerate(body, successors, z3)
    target_models = _enumerate(body, names, z3)

    # Over three nodes the circuits are: three 2-cycles (each leaving one node
    # self-looped) and two 3-cycles -- 5 in all. Each contributes one target
    # model per rotation of its positions, so 3*2 + 2*3 = 12.
    assert source_models == 5, source_models
    assert target_models == 12, target_models
    assert target_models > source_models, (
        "if these are equal the encoding now preserves the count and the "
        "EncodingChoice should say exact() again"
    )


# --- the randomised generator, widened past `or` ----------------------------

def _random_formula(rng, names, depth):
    """A random Boolean formula over @p names, as SMT-LIB text."""
    if depth == 0:
        leaf = rng.choice(names)
        return f"(not {leaf})" if rng.random() < 0.3 else leaf
    gate = rng.choice(["and", "or", "not", "=>", "xor", "=", "ite"])
    sub = lambda: _random_formula(rng, names, depth - 1)
    if gate == "not":
        return f"(not {sub()})"
    if gate == "ite":
        return f"(ite {sub()} {sub()} {sub()})"
    arity = rng.randint(2, 3)
    return "(" + gate + " " + " ".join(sub() for _ in range(arity)) + ")"


def test_cnf_preserves_the_count_over_random_formulas_of_every_gate():
    """The property test above, over a sample space that contains the bugs.

    `test_cnf_preserves_the_count_over_random_formulas` generates DIMACS, and
    the only connective a DIMACS file has is a disjunction of literals. So its
    sample space excluded every gate that could be wrong, and it passed
    throughout while the implication gate's Tseitin definition left its
    variable free -- a defect that multiplied the count for any NESTED `=>`
    and that this generator finds on the first run.

    That is the more useful lesson than the defect: a randomised test is only
    as good as the grammar it samples, and a generator built from the input
    FORMAT rather than from the operators under test will systematically miss
    the operators under test.

    Counted with the parser's own evaluator on both sides, so what is compared
    is what the library thinks a model is.
    """
    import itertools
    import random

    rng = random.Random(20260921)
    names = ["a", "b", "c"]
    decls = "".join(f"(declare-const {n} Bool)" for n in names)

    for _ in range(80):
        # Wrapped in `(or w ...)` so the gate under test is NESTED. At the
        # root the assertion itself pins the gate's definition variable and
        # no one-sidedness is observable -- which is exactly why the defect
        # survived years of satisfiability testing.
        formula = f"(or w {_random_formula(rng, names, 2)})"
        script = f"(set-logic QF_UF)(declare-const w Bool){decls}(assert {formula})"

        src = sp.parse(script)
        asserted = src.assertions[0]
        before = 0
        for bits in itertools.product([False, True], repeat=4):
            model = src.parse_model("(model " + " ".join(
                f"(define-fun {n} () Bool {str(v).lower()})"
                for n, v in zip(["w"] + names, bits)) + ")")
            r = src.evaluate(asserted, model)
            if r is not None and r.is_true:
                before += 1

        tgt = sp.parse(script)
        root, clauses = tgt.to_tseitin_cnf(tgt.assertions[0])
        every = [v.name for v in tgt.variables]
        cnf = tgt.and_(list(clauses) + [root]) if clauses else root
        after = 0
        for bits in itertools.product([False, True], repeat=len(every)):
            model = tgt.parse_model("(model " + " ".join(
                f"(define-fun {n} () Bool {str(v).lower()})"
                for n, v in zip(every, bits)) + ")")
            r = tgt.evaluate(cnf, model)
            if r is not None and r.is_true:
                after += 1

        assert after == before, (
            f"Tseitin changed the model count: {before} -> {after}\n{formula}"
        )


# --- refusals the review found missing --------------------------------------

def test_count_refuses_a_solver_that_cannot_count():
    # The mirror of solve()'s refusal. Without it, .to("z3").count() returns
    # Result(status="sat", count=None) -- a caller who asked HOW MANY gets a
    # result indistinguishable from a counter that failed to report one.
    with pytest.raises(sp.BackendNotFound) as excinfo:
        _counting_formula().to("z3").count(scope="target")
    message = str(excinfo.value)
    assert "not a model counter" in message
    assert "d4" in message


def test_count_refuses_a_weighted_instance_by_name():
    # The DIMACS frontend reads `c p weight` and records it. Counting the
    # formula while ignoring the weights returns the plain count, which
    # answers a different question -- the precise failure this whole subsystem
    # is organised against, and one this API would otherwise have created at
    # the very layer that was taught to read the headers.
    f = sp.read(source="c t wmc\np cnf 2 1\nc p weight 1 0.3 0\n1 2 0\n",
                language="dimacs")
    with pytest.raises(NotImplementedError) as excinfo:
        f.to("d4").count()
    assert "weighted" in str(excinfo.value)


def test_count_refuses_a_projected_instance_by_name():
    f = sp.read(source="c t pmc\np cnf 3 1\nc p show 1 2 0\n1 2 3 0\n",
                language="dimacs")
    with pytest.raises(NotImplementedError) as excinfo:
        f.to("d4").count()
    assert "projected" in str(excinfo.value)


def test_cnf_refuses_an_unused_uninterpreted_function_with_no_assertions():
    # There is no UF application for cnf_atoms() to find. The function table
    # still contributes interpretations to the target model class, so the
    # empty-assertion fast path must reject it before emitting p cnf 0 0.
    f = sp.read(source="(set-logic QF_UF)(declare-fun q (Bool) Bool)",
                language="smtlib2").to("d4")
    with pytest.raises(NotImplementedError, match="function declaration"):
        f.count(scope="target")


def test_cnf_refuses_an_unused_uninterpreted_function_with_assertions():
    # The same omitted interpretation would change the count even when an
    # unrelated proposition supplies a nonempty assertion list.
    f = sp.read(source="(set-logic QF_UF)(declare-const x Bool)"
                       "(declare-fun q (Bool) Bool)(assert x)",
                language="smtlib2")
    with pytest.raises(NotImplementedError, match="function declaration"):
        f.cnf()


def test_raw_parser_classifies_nonrecursive_define_fun_as_func_def():
    # The parser and the HIR round trip both retain deterministic definitions.
    p = sp.parse("(set-logic QF_UF)(declare-const x Bool)"
                 "(define-fun flip ((a Bool)) Bool (not a))")
    flip, = [f for f in p.functions if f.name == "flip"]
    assert flip.is_func_def
    assert not flip.is_func_dec


def test_translated_defined_function_has_a_unique_interpretation_in_cnf():
    # The function is determined by its body and contributes no independent
    # interpretation. Count all emitted CNF variables, including auxiliaries;
    # simply accepting the output would miss free variables introduced here.
    source = "(set-logic QF_UF)(declare-const x Bool)" \
             "(define-fun flip ((a Bool)) Bool (not a))"
    for assertion, expected in (("", 2), ("(assert (flip x))", 1),
                                ("(assert (= x (flip x)))", 0)):
        f = sp.read(source=source + assertion, language="smtlib2")
        assert _models_of_dimacs(f.cnf()) == expected


def test_cnf_refuses_a_used_uninterpreted_function_by_name():
    # A used free function is rejected at the signature gate, before CNF
    # atom abstraction. Its diagnostic must identify the actual blocker.
    f = sp.read(source="(set-logic QF_UF)(declare-const x Bool)"
                       "(declare-const a Bool)(declare-fun q (Bool) Bool)"
                       "(assert (or x (q a)))",
                language="smtlib2")
    with pytest.raises(NotImplementedError, match="function declaration"):
        f.cnf()


def test_cnf_refuses_an_abstracted_theory_atom():
    # No free functions or non-Boolean variables precede this gate: the Int
    # comparison is controlled only by the declared Bool variable. The parser
    # retains the integer ite/equality as a theory atom (mkIte constructs an
    # ITE node and mkEq does not fold non-Boolean operands); Tseitin abstracts
    # it without a defining clause, which must be a named counting refusal.
    f = sp.read(source="(set-logic QF_LIA)(declare-const b Bool)"
                       "(assert (= (ite b 1 0) 1))",
                language="smtlib2")
    with pytest.raises(NotImplementedError) as excinfo:
        f.cnf()
    assert "abstraction" in str(excinfo.value)


def test_cnf_refuses_a_quantifier_as_a_named_refusal():
    # This quantified assertion has no function, free sort, or non-Boolean
    # declaration to trigger an earlier guard, so it reaches the explicit
    # quantifier scan before the CNF engine is called.
    f = sp.read(source="(set-logic UF)(assert (forall ((y Bool)) y))",
                language="smtlib2")
    with pytest.raises(NotImplementedError) as excinfo:
        f.cnf()
    message = str(excinfo.value)
    assert "cannot emit DIMACS" in message
    # The quantifier is FOUND, not guessed at from a failure. The engine's own
    # exception here says only "parse error" (its detail goes to stderr), so a
    # handler that relabelled that as "a quantifier" would say the same thing
    # about an internal error -- the mis-bucketing this tree treats as a
    # defect in its own right.
    assert "forall" in message


@pytest.mark.skipif(sp.backend_path("z3") is None, reason="z3 binary unavailable")
def test_value_returns_the_optimum_not_an_empty_string():
    # `.script()` asks only `(check-sat)`, so a solver that finds an optimum
    # never prints it and `.value()` used to return "" for every successful
    # optimisation -- while its docstring promised the objective's value.
    f = sp.read(source="(set-logic QF_LIA)(declare-const x Int)"
                       "(assert (>= x 3))(minimize x)",
                language="smtlib2")
    assert f.to("z3").value() == 3
    assert f.to("z3").optimize().objectives == {"x": 3}


def test_value_refuses_a_model_with_no_objective():
    # "there is no objective" and "the objective has no value" are different
    # answers, and None cannot say which.
    with pytest.raises(sp.FidelityError) as excinfo:
        _counting_formula().to("z3").value()
    assert "no objective" in str(excinfo.value)


def test_the_objectives_parser_survives_the_shapes_a_solver_prints():
    """An optimum is not always a bare integer, and a name is not always bare.

    Each of these is reachable: `(- 3)` for any negative optimum, `oo` for an
    unbounded one, `(/ 1 2)` under Reals, and `|x[0]|` for every array element
    the XCSP3 frontend emits. Splitting the entry on its first space named
    `|my` and valued `var| 3` -- silently, which is worse than failing.

    Values stay as text unless they are plain integers: coercing `oo` or a
    rational would either raise or lie.
    """
    from somtparser._solving import _parse_objectives as parse

    assert parse("sat\n(objectives\n (x 3)\n)") == {"x": 3}
    assert parse("sat\n(objectives\n (x (- 3))\n)") == {"x": "(- 3)"}
    assert parse("sat\n(objectives\n (x oo)\n)") == {"x": "oo"}
    assert parse("sat\n(objectives\n (x (/ 1 2))\n)") == {"x": "(/ 1 2)"}
    assert parse("sat\n(objectives\n (x 3)\n (y 4)\n)") == {"x": 3, "y": 4}
    assert parse("sat\n(objectives\n (|my var| 3)\n)") == {"|my var|": 3}
    assert parse("sat\n(objectives\n (|x[0]| (- 7))\n)") == {"|x[0]|": "(- 7)"}
    # No objectives block at all -- a plain `.solve()` reply.
    assert parse("sat\n") == {}
    assert parse("sat\n(objectives\n)") == {}

    # A COMPOUND objective term. This is the ordinary case, not an exotic one:
    # `OmtEmitter` renders `(minimize <term text>)`, so every summed objective
    # -- every MaxSAT cost function, every OPB/WBO instance with one -- comes
    # back with an s-expression where a symbol would be. Splitting the entry on
    # its first space made the key `(+` and the value `x y) 5`, and `.value()`
    # returned that string as if it were the optimum.
    #
    # This case is here because the first version of this test did not have it,
    # and the reason is worth naming: its shapes were enumerated from a list of
    # what might break, not from the grammar of what `(objectives ...)` can
    # actually contain. That is the same mistake as generating DIMACS files to
    # test gates that DIMACS cannot express.
    assert parse("sat\n(objectives\n ((+ x y) 5)\n)") == {"(+ x y)": 5}
    assert parse("sat\n(objectives\n ((* 3 x) 9)\n)") == {"(* 3 x)": 9}
    assert parse("sat\n(objectives\n ((+ x y) 5)\n (z 2)\n)") == {
        "(+ x y)": 5, "z": 2}
    # ...and a nested term, so the balance is really being tracked.
    assert parse("sat\n(objectives\n ((+ (* 2 x) y) 11)\n)") == {
        "(+ (* 2 x) y)": 11}


def _assert_dimacs_header_and_literals_are_consistent(text):
    lines = [line for line in text.splitlines() if line.strip()]
    headers = [line.split() for line in lines if line.startswith("p cnf ")]
    assert len(headers) == 1
    nvars, nclauses = int(headers[0][2]), int(headers[0][3])
    clauses = [line.split() for line in lines if line[0] not in ("p", "c")]
    assert len(clauses) == nclauses
    for row in clauses:
        assert row[-1] == "0"
        assert all(0 < abs(int(literal)) <= nvars for literal in row[:-1])


def _repeated_cnf_formula():
    return sp.read(
        source="(set-logic QF_UF)"
               "(declare-const w Bool)(declare-const a Bool)(declare-const b Bool)"
               "(assert (or w (and a b)))",
        language="smtlib2",
    )


def test_formula_cnf_is_conversion_local_across_calls_and_to_siblings():
    # w OR (a AND b) has five assignments over its three declared Boolean
    # variables. The Formula and .to() sibling share the same Translation;
    # CNF emission must still use fresh conversion-local parser state each time.
    formula = _repeated_cnf_formula()
    sibling = formula.to("d4")
    assert sibling._t is formula._t
    parser = formula.translation.parser
    original_dump = parser.dump_smt2()
    original_variables = [(v.name, str(v.sort), v.is_temp_var)
                          for v in parser.variables]
    original_atoms = list(parser.cnf_atoms())

    for emitted in (formula.cnf(), formula.cnf(), sibling.cnf(), sibling.cnf()):
        _assert_dimacs_header_and_literals_are_consistent(emitted)
        assert _models_of_dimacs(emitted) == 5

    assert parser.dump_smt2() == original_dump
    assert [(v.name, str(v.sort), v.is_temp_var)
            for v in parser.variables] == original_variables
    assert parser.cnf_atoms() == original_atoms


def test_cnf_temp_name_skips_a_declared_temp_0_variable():
    # The source's declared `temp_0` is an ordinary counted Boolean. The first
    # generated Tseitin name must skip it, keeping DIMACS names and indices
    # one-to-one. The known source count and header bounds make this non-vacuous.
    formula = sp.read(
        source="(set-logic QF_UF)"
               "(declare-const temp_0 Bool)(declare-const p Bool)(declare-const q Bool)"
               "(assert (or temp_0 (and p q)))",
        language="smtlib2",
    )
    parser = formula.translation.parser
    before = [(v.name, str(v.sort), v.is_temp_var) for v in parser.variables]
    original_dump = parser.dump_smt2()
    emitted = formula.cnf()
    _assert_dimacs_header_and_literals_are_consistent(emitted)
    assert _models_of_dimacs(emitted) == 5
    assert [v.name for v in parser.declared_variables] == ["temp_0", "p", "q"]
    assert [(v.name, str(v.sort), v.is_temp_var) for v in parser.variables] == before
    assert parser.dump_smt2() == original_dump


def test_reparsed_cnf_keeps_unused_boolean_declarations_in_its_vocabulary():
    # Exercise the nonempty assertion path: three used variables yield five
    # satisfying assignments, and an unused fourth declared Boolean doubles
    # that target assignment count to ten.
    formula = sp.read(
        source="(set-logic QF_UF)"
               "(declare-const w Bool)(declare-const a Bool)"
               "(declare-const b Bool)(declare-const unused Bool)"
               "(assert (or w (and a b)))",
        language="smtlib2",
    )
    emitted = formula.cnf()
    _assert_dimacs_header_and_literals_are_consistent(emitted)
    assert int(emitted.splitlines()[0].split()[2]) > 4
    assert _models_of_dimacs(emitted) == 10
    assert [v.name for v in formula.translation.parser.declared_variables] == [
        "w", "a", "b", "unused"]


def test_zero_assertions_keep_unused_boolean_declarations_in_the_cnf_vocabulary():
    formula = sp.read(
        source="(set-logic QF_UF)(declare-const unused_a Bool)"
               "(declare-const unused_b Bool)",
        language="smtlib2",
    )
    before = formula.translation.parser.dump_smt2()
    emitted = formula.cnf()
    assert emitted == "p cnf 2 0\n"
    assert _models_of_dimacs(emitted) == 4
    assert formula.translation.parser.dump_smt2() == before
