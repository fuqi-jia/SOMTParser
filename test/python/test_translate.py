"""Bindings for the multi-language frontend.

The C++ side never throws across an API boundary, but Python callers expect
exceptions, so strict=True opts into them while the default stays value-based.
"""
import json

import pytest

import somtparser as sp

_FLIP = {">=": "<=", ">": "<", "<=": ">=", "<": ">"}


def var_bounds(assertions):
    """Read each assertion as the claim it makes about one variable.

    Counting assertions cannot see the difference between "x >= 1 and x <= 5"
    and the swapped, trivially UNSAT "x <= 1 and x >= 5": both leave the count,
    the fidelity flags and every recorded Bound identical. Builders hash-cons,
    fold and may reorder arguments, so read the variable's side and flip the
    relation when it lands on the right: (>= x 1) and (<= 1 x) both become
    ("x", ">=", "1").
    """
    out = []
    for a in assertions:
        if a.kind not in _FLIP or a.num_children != 2:
            continue
        lhs, rhs = a.children
        if lhs.is_var and rhs.is_const:
            out.append((lhs.name, a.kind, rhs.name))
        elif rhs.is_var and lhs.is_const:
            out.append((rhs.name, _FLIP[a.kind], lhs.name))
    return out


def test_languages_and_profiles_are_listed():
    langs = sp.languages()
    assert "minizinc" in langs
    profiles = sp.profiles()
    assert "default" in profiles
    assert "strict" in profiles
    assert "bv32" in profiles


def test_coverage_reports_missing_constructs():
    # The counts and the list are two spellings of one fact, so they have to
    # agree: a frontend that raises `supported` without striking the construct
    # off `missing` claims a gap it has closed, and one that adds a name without
    # lowering `supported` hides a gap behind a full count. Both are silent.
    #
    # This replaces `"array" in coverage("minizinc")["missing"]`, which named a
    # specific gap and so went stale the moment MiniZinc reached 8/8 -- and went
    # stale unnoticed, because the pytest run was using a `.so` built before the
    # change.
    gaps = 0
    for language in sp.languages():
        cov = sp.coverage(language)
        assert cov["total"] >= cov["supported"], language
        assert len(cov["missing"]) == cov["total"] - cov["supported"], language
        gaps += len(cov["missing"])
    # And the mechanism is exercised rather than vacuously satisfied by a tree
    # in which every language happens to be complete.
    assert gaps > 0


def test_source_semantics_cover_every_registered_language():
    for language in sp.languages():
        spec = sp.source_semantics(language)
        assert spec.valid
        assert spec.institution.id
        assert spec.institution.object_logic
        assert spec.institution.model_class
        assert spec.institution.satisfaction_relation
        assert spec.institution.assumptions.id
        assert spec.rationale

    mzn = sp.source_semantics("minizinc")
    assert mzn.institution.assumptions.functions == sp.FunctionSemantics.PARTIAL
    assert (mzn.institution.assumptions.carrier_emptiness
            == sp.CarrierEmptiness.MIXED)
    assert (mzn.institution.assumptions.undefined
            == sp.UndefinedSemantics.RELATIONAL_FALSE)
    assert (mzn.institution.assumptions.division
            == sp.DivisionSemantics.TRUNCATE_TOWARD_ZERO)
    smt = sp.source_semantics("smtlib2")
    assert (smt.institution.assumptions.carrier_emptiness
            == sp.CarrierEmptiness.NONEMPTY)

    hddl = sp.source_semantics("hddl")
    assert hddl.decisions == [sp.DecisionKind.PLAN_EXISTENCE, sp.DecisionKind.OPTIMIZATION]
    assert hddl.required_bounds == [sp.Bound.PLAN_HORIZON,
                                    sp.Bound.DECOMPOSITION_DEPTH]
    assert hddl.institution.assumptions.arithmetic == sp.ArithmeticSemantics.RATIONAL
    assert sp.source_semantics("pddl").institution.assumptions.arithmetic == sp.ArithmeticSemantics.REAL

    sygus = sp.source_semantics("sygus")
    assert sygus.decisions == [sp.DecisionKind.FUNCTION_SYNTHESIS]
    assert (sygus.smt_embedding
            == sp.SmtEmbeddingKind.DIRECT_REDUCTION)
    assert sygus.required_bounds == [sp.Bound.GRAMMAR_RESTRICTION]
    assert "exact inductive AST encoding" in sygus.rationale

    syntcomp = sp.source_semantics("syntcomp")
    assert syntcomp.decisions == [sp.DecisionKind.REACTIVE_REALIZABILITY]
    assert (syntcomp.smt_embedding
            == sp.SmtEmbeddingKind.DIRECT_REDUCTION)
    assert syntcomp.required_bounds == []

    assert mzn.supports(sp.DecisionKind.SATISFIABILITY)
    assert mzn.supports(sp.DecisionKind.OPTIMIZATION)
    assert not mzn.supports(sp.DecisionKind.VALIDITY)

    with pytest.raises(ValueError, match="no semantic specification"):
        sp.source_semantics("unknown")


def test_translate_source_end_to_end():
    t = sp.translate(source="var 1..5: x;\nconstraint x > 2;\nsolve minimize x;\n",
                     language="minizinc")
    assert t.ok
    # Two domain bounds plus the constraint -- and the bounds say what the
    # domain said. "var 1..5" must become x >= 1 and x <= 5; the swapped form
    # is UNSAT while leaving this count and the whole report unchanged.
    assert len(t.parser.assertions) == 3
    bounds = var_bounds(t.parser.assertions)
    assert ("x", ">=", "1") in bounds
    assert ("x", "<=", "5") in bounds
    assert ("x", "<=", "1") not in bounds
    assert ("x", ">=", "5") not in bounds
    assert ("x", ">", "2") in bounds
    assert t.report.provenance.language_id == "minizinc"
    assert t.report.provenance.profile_id == "default"
    assert t.report.provenance.profile_content_hash
    assert t.report.provenance.target_dialect == "smtlib-omt-2025"


def test_fidelity_is_exposed_as_two_axes():
    t = sp.translate(source="var int: x;\nconstraint x > 0;\nsolve satisfy;\n",
                     language="minizinc")
    assert t.report.fidelity.sound is True
    assert t.report.fidelity.complete is True
    assert t.report.fidelity.bounds == []


def test_dialects_re_emit_without_retranslating():
    t = sp.translate(source="var 1..5: x;\nsolve minimize x;\n", language="minizinc")
    standard = t.to_smt2()
    assert "define-objective" in standard
    z3 = t.to_smt2(dialect=sp.OmtDialect.Z3)
    assert "(minimize " in z3
    assert "define-objective" not in z3
    assert "minimize" not in t.to_smt2(dialect=sp.OmtDialect.NONE)


def test_report_json_round_trips():
    t = sp.translate(source="var int: x;\nsolve satisfy;\n", language="minizinc")
    data = json.loads(t.report.to_json())
    assert data["provenance"]["language_id"] == "minizinc"
    assert set(data["fidelity"]) >= {"sound", "complete", "bounds"}
    assert "hir_feature_counts" in data


def test_failure_is_a_value_by_default_and_an_exception_when_strict():
    t = sp.translate(source="var int: ;\n", language="minizinc")
    assert not t.ok
    assert t.diagnostic_items[0].code == sp.ErrorCode.E_PARSE
    assert t.diagnostic_items[0].line == 1

    with pytest.raises(sp.TranslationError) as excinfo:
        sp.translate(source="var int: ;\n", language="minizinc", strict=True)
    assert excinfo.value.code == sp.ErrorCode.E_PARSE


def test_unreadable_data_file_stops_the_translation():
    # MiniZinc reads .dzn now, so the guard that refused any unit carrying one
    # is gone -- but the risk it protected against is not. A data file that
    # cannot be read must STOP the translation rather than be passed over,
    # which would translate the model half alone and report success for a
    # problem it never fully read.
    t = sp.translate(source="var int: x;\nconstraint x > 0;\nsolve satisfy;\n",
                     language="minizinc", data=["m.dzn"])
    assert not t.ok
    assert t.diagnostic_items[0].code == sp.ErrorCode.E_IO
    assert "m.dzn" in t.diagnostic_items[0].message

    # The identical call without the data file still succeeds, so what fails
    # above is the dropped data and not the model.
    assert sp.translate(source="var int: x;\nconstraint x > 0;\nsolve satisfy;\n",
                        language="minizinc").ok


def test_bv32_profile_bounds_unbounded_ints_with_incomplete_fidelity():
    # This is the one end-to-end proof, anywhere in the suite, that a
    # successful translate() call can produce sound != complete: bound-ints
    # clamps "x" to a signed 32-bit range, which keeps every found solution
    # real (sound) while excluding solutions outside that range (not complete).
    t = sp.translate(source="var int: x;\nconstraint x > 0;\nsolve satisfy;\n",
                     language="minizinc", profile="bv32")
    assert t.ok
    assert t.report.fidelity.sound is True
    assert t.report.fidelity.complete is False        # this line is why this task exists
    assert len(t.report.fidelity.bounds) == 1
    # kind is what makes value readable: 32 is a bit width under BV_WIDTH and a
    # step count under BMC_DEPTH, and the eval pipeline stratifies on which.
    assert t.report.fidelity.bounds[0].kind == sp.Bound.Kind.BV_WIDTH
    assert t.report.fidelity.bounds[0].value == 32
    assert t.report.fidelity.bounds[0].site == "x"

    # The pass choice is reachable as an attribute, alongside the semantic
    # translation stages now carried by the same report.
    choice = next(c for c in t.report.choices if c.strategy == "bound-ints")
    assert choice.site == "x"
    assert choice.unified_op == "int-var"
    assert choice.fidelity.complete is False
    assert choice.fidelity.bounds[0].kind == sp.Bound.Kind.BV_WIDTH

    # Every semantically distinct search limit is exposed to Python. In
    # particular, a planning horizon must not be confused with HTN expansion,
    # grammar enumeration, or reactive strategy size.
    assert sp.Bound.Kind.PLAN_HORIZON == sp.Bound.PLAN_HORIZON
    assert (sp.Bound.Kind.DECOMPOSITION_DEPTH
            == sp.Bound.DECOMPOSITION_DEPTH)
    assert (sp.Bound.Kind.GRAMMAR_RESTRICTION
            == sp.Bound.GRAMMAR_RESTRICTION)
    assert sp.Bound.Kind.STRATEGY_SIZE == sp.Bound.STRATEGY_SIZE

    # stats and warnings are bound too; the aggregate report is one object.
    assert t.report.stats.num_vars == 1
    assert t.report.stats.num_constraints == 1
    assert t.report.stats.num_objectives == 0
    assert t.report.warnings == []

    # ...and the JSON view still agrees with the attributes.
    data = json.loads(t.report.to_json())
    assert data["fidelity"]["complete"] is False
    json_choice = next(c for c in data["choices"] if c["strategy"] == "bound-ints")
    assert json_choice["site"] == "x"

    # The clamp reached the emitted formula in the right direction: signed
    # 32-bit is [-2**31, 2**31-1], not the swapped, always-UNSAT reverse.
    bounds = var_bounds(t.parser.assertions)
    assert ("x", ">=", str(-(2 ** 31))) in bounds
    assert ("x", "<=", str(2 ** 31 - 1)) in bounds
    assert ("x", "<=", str(-(2 ** 31))) not in bounds
    assert ("x", ">=", str(2 ** 31 - 1)) not in bounds


def test_unknown_language_and_profile_are_rejected():
    t = sp.translate(source="x", language="nope")
    assert not t.ok
    t2 = sp.translate(source="var int: x;\nsolve satisfy;\n",
                      language="minizinc", profile="nope")
    assert not t2.ok
    assert t2.diagnostic_items[0].code == sp.ErrorCode.E_PASS_PIPELINE


def test_parser_parse_any():
    p = sp.Parser()
    assert p.parse_any("languages/minizinc/instances/ok/trivial.mzn")
    assert p.last_translation_report.provenance.language_id == "minizinc"
    # A successful translation records no error, which is what makes the
    # failing case below evidence of anything.
    assert not [w for w in p.last_translation_report.warnings
                if w.severity == sp.Severity.ERROR]


def test_parse_any_failure_is_recorded_in_the_report():
    """A source-language parse error must be readable from the report.

    parse_any returns False, but a caller that inspects last_translation_report
    instead used to see an empty, exact-fidelity report -- indistinguishable
    from a translation that succeeded. The diagnostics translate() recorded die
    with the Translation object unless they are copied across.
    """
    p = sp.Parser()
    assert not p.parse_any("languages/minizinc/instances/reject/bad_syntax.mzn")
    errors = [w for w in p.last_translation_report.warnings
              if w.severity == sp.Severity.ERROR]
    assert errors, "a failed parse_any left no record in the report"
    # The recorded content, not merely its existence: the message must say what
    # went wrong, and it must not be filed as an internal defect.
    assert all(e.code != sp.ErrorCode.E_INTERNAL for e in errors)
    assert any(e.message for e in errors)


def test_last_translation_report_survives_the_next_parse_any():
    """The report must outlive the call that replaced it.

    The property was bound with pybind11's default for a property,
    return_value_policy::reference_internal, which keeps the *Parser* alive but
    not the shared_ptr owning the report. Parser::last_report_ is the sole
    owner and is reassigned by the next parse_any, so a Python name bound to an
    earlier report pointed into freed memory: touching it was a
    heap-use-after-free and, in practice, a interpreter SIGSEGV.

    Reading the JSON before *and* after is what makes this a test rather than a
    crash-or-not coin flip: a dangling read can return plausible garbage.
    """
    p = sp.Parser()
    assert p.parse_any("languages/minizinc/instances/ok/trivial.mzn")
    first = p.last_translation_report
    before = first.to_json()
    assert before

    assert p.parse_any("languages/minizinc/instances/ok/trivial.mzn")
    assert first.to_json() == before
    assert first.provenance.language_id == "minizinc"


def test_parse_any_twice_does_not_lose_track_of_objectives():
    """parse_any checks what it added, not the parser's total.

    The guard compared getObjectives().size() against the model's objective
    count, so a Parser that already held objectives -- from an earlier
    parse_any, or from parse_string("(minimize y)"), which the header documents
    -- failed with `E_INTERNAL: 1 objective(s) ... but 2 landed` although both
    had landed correctly.
    """
    p = sp.Parser()
    path = "languages/minizinc/instances/ok/trivial.mzn"
    assert p.parse_any(path)
    assert len(p.objectives) == 1
    assert p.parse_any(path)
    assert len(p.objectives) == 2
    assert not [w for w in p.last_translation_report.warnings
                if w.severity == sp.Severity.ERROR]


def test_ill_sorted_input_is_a_diagnostic_not_a_crash(capfd):
    """An ill-sorted model must not abort the process or print to stdout.

    `var bool: b; constraint b + 1 > 0;` used to reach Parser::mkAdd, which
    printed `error: Kind mismatch ...` to stdout -- corrupting the SMT-LIB
    stream a caller pipes onward -- and then threw, aborting with SIGABRT.
    Through these bindings that killed the interpreter.

    capfd, not capsys: the write came from C++ on file descriptor 1, which a
    Python-level capture does not see.
    """
    t = sp.translate(path="languages/minizinc/instances/reject/ill_sorted.mzn")
    assert not t.ok
    assert t.diagnostic_items
    assert t.diagnostic_items[0].code == sp.ErrorCode.E_TYPE
    # The diagnostic names the term, not just the file: Expr::loc was set by
    # nothing before, so every message pointed at line 0.
    assert t.diagnostic_items[0].line > 0
    assert t.diagnostic_items[0].file.endswith("ill_sorted.mzn")

    captured = capfd.readouterr()
    assert captured.out == ""


def test_provenance_is_importable():
    """Declared in the .pyi and bound in C++, but missing from the package.

    A type checker accepted `somtparser.Provenance` while it raised
    AttributeError at runtime -- the worst combination, because the stub is
    what a caller reads.
    """
    assert sp.Provenance is not None
    assert "Provenance" in sp.__all__
    p = sp.Parser()
    assert p.parse_any("languages/minizinc/instances/ok/trivial.mzn")
    assert isinstance(p.last_translation_report.provenance, sp.Provenance)
