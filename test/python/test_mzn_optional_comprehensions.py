"""Source-semantics tests for fixed-shape arrays with variable occurrence.

These are independent formulas from the MiniZinc option-type specification.
Partial-head boundary probes are retained separately for the official compiler.
"""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _solver(source):
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [diagnostic.message for diagnostic in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    return solver


@pytest.mark.parametrize("indexed", [False, True], ids=["sequence", "indexed"])
@pytest.mark.parametrize("present", [False, True], ids=["absent", "present"])
def test_occurrence_and_value_are_independent(indexed, present):
    head = "i:10+i" if indexed else "10+i"
    source = ("var bool:b;constraint b=" + str(present).lower()
              + ";any:a=[" + head + "|i in 1..3 where b];"
              + "constraint length([" + head + "|i in 1..3 where b])=3;"
              + "constraint length(a)=3;constraint "
              + ("occurs(a[2]) /\\ deopt(a[2])=12" if present
                 else "absent(a[2]) /\\ (a[2] default 9)=9")
              + ";solve satisfy;")
    solver = _solver(source)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("check", [
    "forall(i in 1..3)(occurs(a[i]) <-> b)",
    "forall(i in 1..3)(absent(a[i]) <-> not b)",
    "forall(i in 1..3)((a[i] default 7)=(if b then i else 7 endif))",
    "sum(a)=(if b then 6 else 0 endif)",
    "product(a)=(if b then 6 else 1 endif)",
    "((a[2]=2) <-> b)",
    "((a[2]!=2) <-> not b)",
    "((a[2]<0) <-> not b)",
])
def test_universal_independent_characterization(check):
    solver = _solver("var bool:b;any:a=[i:i|i in 1..3 where b];"
                     "constraint not(" + check + ");solve satisfy;")
    assert solver.check() == z3.unsat, solver.reason_unknown()


@pytest.mark.parametrize("condition", [r"i=1 /\ b", r"b /\ i=1"])
def test_variable_filter_compacts_parameter_false_tuples(condition):
    solver = _solver("var bool:b;any:a=[i:i|i in 1..2 where " + condition + "];"
                     r"constraint not(length(a)=1 /\ (occurs(a[1]) <-> b));"
                     "solve satisfy;")
    assert solver.check() == z3.unsat


def test_static_filter_still_compacts_before_dynamic_occurrence():
    solver = _solver(r"var bool:b;any:a=[i*10+j|i in 1..2 where b,j in 1..2 where j=1];"
                     r"constraint not(length(a)=2 /\ (occurs(a[1]) <-> b) /\ "
                     r"(deopt(a[1])=11 <-> b) /\ (deopt(a[2])=21 <-> b));solve satisfy;")
    assert solver.check() == z3.unsat


def test_dynamic_read_preserves_source_indices_and_occurrence():
    solver = _solver(r"var bool:b;var 4..6:k;any:a=[i:2*i|i in 4..6 where b];"
                     r"constraint not((occurs(a[k]) <-> b) /\ "
                     r"((a[k] default -1)=(if b then 2*k else -1 endif)));solve satisfy;")
    assert solver.check() == z3.unsat


def test_index_key_reordering_keeps_presence_with_value():
    solver = _solver(r"var bool:b;any:a=[4-i:i|i in 1..3 where b \/ i=1];"
                     r"constraint not(occurs(a[3]) /\ deopt(a[3])=1 /\ "
                     r"(occurs(a[1]) <-> b) /\ ((a[1] default 9)=(if b then 3 else 9 endif)));"
                     "solve satisfy;")
    assert solver.check() == z3.unsat


def test_reindex_reverse_and_concat_preserve_optional_cells():
    solver = _solver(r"var bool:b;any:a=[i:i|i in 4..6 where b];"
                     r"any:c=array1d(1..3,reverse(a)) ++ [10];"
                     r"constraint not(length(c)=4 /\ deopt(c[4])=10 /\ "
                     r"((c[1] default 0)=(if b then 6 else 0 endif)) /\ "
                     r"sum(c)=(if b then 25 else 10 endif));solve satisfy;")
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("fn,expected", [("forall", "not b"), ("exists", "false")])
def test_absent_boolean_cells_use_logical_identity(fn, expected):
    solver = _solver("var bool:b;any:a=[i:false|i in 1..3 where b];constraint not("
                     + fn + "(a) <-> (" + expected + "));solve satisfy;")
    assert solver.check() == z3.unsat


def test_nested_filters_conjoin_occurrence():
    solver = _solver(r"var bool:b;var bool:c;any:a=[i:i|i in 1..2 where b];"
                     r"any:d=[i:a[i]|i in 1..2 where c];"
                     r"constraint not((occurs(d[1]) <-> (b /\ c)) /\ "
                     r"((d[2] default 9)=(if b /\ c then 2 else 9 endif)));solve satisfy;")
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("present,expected", [(False, z3.sat), (True, z3.unsat)])
def test_all_different_ignores_absent_duplicates(present, expected):
    solver = _solver('include "all_different.mzn";var bool:b;constraint b='
                     + str(present).lower() + ';any:a=[i:5|i in 1..3 where b];'
                     'constraint all_different(a);solve satisfy;')
    assert solver.check() == expected


def test_all_different_symbolic_integer_relation():
    solver = _solver(r'include "all_different.mzn";var bool:b;var bool:c;'
                     r'var int:x;var int:y;any:a=[i:if i=1 then x else y endif|'
                     r'i in 1..2 where if i=1 then b else c endif];'
                     r'constraint not(all_different(a) <-> (not(b /\ c) \/ x!=y));solve satisfy;')
    assert solver.check() == z3.unsat


def test_all_different_keeps_linear_native_distinct():
    source = ('include "all_different.mzn";var bool:b;'
              'any:a=[i:i|i in 1..128 where b];constraint all_different(a);solve satisfy;')
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [diagnostic.message for diagnostic in translated.diagnostic_items]
    smt = translated.to_smt2()
    assert smt.count("(distinct ") == 1


def test_absence_is_defined_but_deopt_is_partial():
    solver = _solver(r"var bool:b;constraint not b;any:a=[i:5|i in 1..1 where b];"
                     r"constraint absent(a[1]) /\ not(deopt(a[1])=5);solve satisfy;")
    assert solver.check() == z3.sat


    # Direct shape observations still evaluate a selected numeric head.
    for present, expected in ((False, z3.sat), (True, z3.unsat)):
        for head in ("1 div d", "i:1 div d"):
            solver = _solver("var bool:b;constraint b=" + str(present).lower()
                             + ";var 0..0:d;constraint length([" + head
                             + "|i in 1..1 where b])=1;solve satisfy;")
            assert solver.check() == expected


def test_empty_variable_filter_preserves_typed_empty_shape():
    solver = _solver(r"var bool:b;any:a=[i:i|i in 1..0 where b];"
                     r"constraint length(a)=0 /\ sum(a)=0 /\ product(a)=1;solve satisfy;")
    assert solver.check() == z3.sat


def test_real_optional_sum_retains_exact_value():
    solver = _solver(r"var bool:b;any:a=[i:1.5|i in 1..2 where b];"
                     r"constraint not(sum(a)=(if b then 3.0 else 0.0 endif));solve satisfy;")
    assert solver.check() == z3.unsat


def test_direct_indexed_aggregate_uses_presence():
    solver = _solver(r"var bool:b;constraint not(sum([i:i|i in 1..3 where b])="
                     r"(if b then 6 else 0 endif));solve satisfy;")
    assert solver.check() == z3.unsat


def test_strict_optional_array_equality():
    solver = _solver(r"var bool:b;any:a=[i:i|i in 1..2 where b];"
                     r"constraint not((a=[1,2]) <-> b);solve satisfy;")
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("negated,expected", [(False, z3.unsat), (True, z3.sat)])
def test_invalid_optional_index_is_undefined_not_absent(negated, expected):
    observer = "absent(a[k])"
    if negated:
        observer = "not(" + observer + ")"
    solver = _solver("var bool:b;constraint not b;var 7..7:k;"
                     "any:a=[i:i|i in 4..6 where b];constraint "
                     + observer + ";solve satisfy;")
    assert solver.check() == expected


@pytest.mark.parametrize("consumer", ["forall(a)", "forall(array1d(1..0,a))"])
def test_empty_optional_int_array_keeps_its_numeric_signature(consumer):
    translated = sp.translate(source="var bool:b;any:a=[i:i|i in 1..0 where b];constraint "
                              + consumer + ";solve satisfy;", language="minizinc")
    assert not translated.ok
    assert any("signature" in diagnostic.message for diagnostic in translated.diagnostic_items)


def test_empty_optional_concat_keeps_its_element_type():
    translated = sp.translate(source="var bool:b;any:a=[i:i|i in 1..0 where b];"
                              "any:c=[] ++ a;constraint forall(c);solve satisfy;", language="minizinc")
    assert not translated.ok
    assert any("signature" in diagnostic.message for diagnostic in translated.diagnostic_items)


@pytest.mark.parametrize("present,expected", [(False, "sat"), (True, "unsat")])
def test_default_distinguishes_absence_from_undefined_present_cell(present, expected):
    # The official compiler permits the fallback only while the cell is absent.
    for index, declaration in (("1", ""), ("k", "var 1..1:k;")):
        solver = _solver("var bool:b;constraint b=" + str(present).lower()
                         + ";var 0..0:d;" + declaration
                         + "any:a=[i:1 div d|i in 1..1 where b];"
                         + "constraint (a[" + index + "] default 9)=9;solve satisfy;")
        assert str(solver.check()) == expected
    # Scalar index failure remains recoverable by default. It is distinct
    # from constructing a present cell whose numeric head is undefined.
    recovery = _solver("var bool:b;constraint not b;any:a=[i:5|i in 1..1 where b];"
                       "constraint (a[2] default 9)=9;solve satisfy;")
    assert str(recovery.check()) == "sat"


@pytest.mark.parametrize("index", [0, 2])
@pytest.mark.parametrize("observer,expected", [
    ("occurs", "unsat"), ("absent", "unsat"),
    ("not occurs", "sat"), ("not absent", "sat"),
])
def test_constant_invalid_optional_index_is_partial_not_refused(index, observer, expected):
    solver = _solver("var bool:b;constraint not b;any:a=[i:i|i in 1..1 where b];"
                     + "constraint " + observer + "(a[" + str(index) + "]);solve satisfy;")
    assert str(solver.check()) == expected


def test_original_static_filter_contradiction_translates_to_unsat():
    solver = _solver(r"var bool:b;any:a=[i:i|i in 1..2 where (i=1 /\ b)];"
                     r"constraint not b /\ length(a)=2 /\ absent(a[1]) /\ absent(a[2]);solve satisfy;")
    assert str(solver.check()) == "unsat"
