"""The JSON HIR entry point preserves chain equality and its negation."""
import pytest
import z3
from somtparser.hir import HirBuilder


@pytest.mark.parametrize("sort,smt_sort", [
    ("Int", "Int"), ("Real", "Real"), ("Bool", "Bool"),
    ("String", "String"), ({"BitVec": 8}, "(_ BitVec 8)"),
])
@pytest.mark.parametrize("negated", [False, True])
def test_json_hir_equality_matches_independent_chain(sort, smt_sort, negated):
    builder = HirBuilder()
    names = ["a", "b", "c", "d"]
    for name in names:
        builder.declare(name, sort)
    equal = {"op": "eq", "args": [{"var": name} for name in names]}
    builder.constrain({"op": "not", "args": [equal]} if negated else equal)
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    reference = ''.join(f'(declare-const {name} {smt_sort})' for name in names)
    chain = '(and (= a b) (= b c) (= c d))'
    reference += '(assert ' + ('(not ' + chain + ')' if negated else chain) + ')'
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())),
                     z3.And(*z3.parse_smt2_string(reference))))
    assert solver.check() == z3.unsat
