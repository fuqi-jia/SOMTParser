"""SMT source macros retain their executable bodies and observable semantics."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def emit(source):
    result = sp.translate(source=source, language="smtlib2")
    assert result.ok, [d.message for d in result.diagnostic_items]
    output = result.to_smt2(sp.OmtDialect.Z3)
    sp.parse(output)  # native self-read is a separate contract from Z3 parsing
    return output


@pytest.mark.parametrize("source", [
    "(set-logic QF_LIA)(declare-const x Int)(define-fun inc ((x Int)) Int (+ x 1))(assert (= x 2))(assert (= (inc x) 3))(check-sat)",
    "(set-logic QF_LRA)(declare-const x Real)(define-fun half ((x Real)) Real (/ x 2))(assert (= x 3))(assert (= (half x) (/ 3 2)))(check-sat)",
    "(set-logic QF_BV)(declare-const x (_ BitVec 8))(define-fun flip ((x (_ BitVec 8))) (_ BitVec 8) (bvnot x))(assert (= x #x05))(assert (= (flip x) #xfa))(check-sat)",
    "(set-logic QF_UFLIA)(declare-fun u (Int) Int)(define-fun inc ((x Int)) Int (+ (u x) 1))(assert (= (u 2) 3))(assert (= (inc 2) 4))(check-sat)",
    "(set-logic QF_LIA)(declare-const x Int)(define-fun offset ((x Int)) Int (let ((y x)(x 9)) (- y x)))(assert (= x 10))(assert (= (offset x) 1))(check-sat)",
])
def test_macro_translation_has_no_definitional_quantifier_and_both_models_work(source):
    output = emit(source)
    assert "(forall " not in output
    assert "(define-fun " in output
    assert output.count("(assert ") == source.count("(assert ")
    context = z3.Context()
    formulas = [z3.parse_smt2_string(text, ctx=context) for text in (source, output)]
    for own in formulas:
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(own)
        assert solver.check() == z3.sat
        model = solver.model()
        for other in formulas:
            assert all(z3.is_true(model.eval(assertion, model_completion=True)) for assertion in other)
    difference = z3.Solver(ctx=context)
    difference.set(timeout=5000)
    difference.add(z3.Xor(z3.And(*formulas[0]), z3.And(*formulas[1])))
    assert difference.check() == z3.unsat


def test_defined_omt_terms_keep_lex_order_query_and_optimum():
    source = """(set-logic QF_LIA)(set-option :opt.priority lex)
    (declare-const x Int)(define-fun shifted ((v Int)) Int (- v 2))
    (assert (and (>= x 0) (<= x 4)))
    (minimize (shifted x))(maximize x)(check-sat)(get-objectives)"""
    output = emit(source)
    assert "(define-fun shifted " in output
    assert output.index("(minimize ") < output.index("(maximize ") < output.index("(check-sat)") < output.index("(get-objectives)")
    assert len(sp.parse(output).objectives) == 2
    values = []
    for text in (source, output):
        context = z3.Context()
        solver = z3.Optimize(ctx=context)
        solver.set(timeout=5000)
        solver.from_string(text)
        assert solver.check() == z3.sat
        values.append(solver.model().eval(z3.Int("x", ctx=context)).as_long())
    assert values == [0, 0]


def test_pop_removes_definition_without_reordering_dependency():
    source = """(declare-const x Int)(define-fun first ((n Int)) Int (+ n 1))
    (define-fun second ((n Int)) Int (first (first n)))
    (push 1)(define-fun removed () Int 9)(pop 1)
    (assert (= x 2))(assert (= (second x) 4))(check-sat)"""
    output = emit(source)
    assert "removed" not in output
    assert output.index("(define-fun first ") < output.index("(define-fun second ") < output.index("(assert ")
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(output, ctx=context))
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int("x", ctx=context)).as_long() == 2
