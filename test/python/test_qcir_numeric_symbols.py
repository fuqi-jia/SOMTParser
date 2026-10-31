"""Independent solver checks for QCIR numeric binder emission and prefix order."""
from _public_relation import public_relation
import pytest
import z3
import somtparser as sp


@pytest.mark.parametrize('header', ['#QCIR-G14\n', '# Move variables:\n', ''])
@pytest.mark.parametrize('prefix,expected', [
    ('forall(1)\nexists(2)\n', z3.sat),
    ('exists(2)\nforall(1)\n', z3.unsat),
])
def test_numeric_quantifier_dependency(header, prefix, expected):
    result = sp.translate(source=header + prefix + 'output(3)\n3 = xor(1,2)\n',
                          language='qcir', options={'allow_missing_header': 'true'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == expected


def test_numeric_free_and_local_bound_names_remain_distinct():
    # Identifiers 1 and 01 are distinct strings, not equal integer constants.
    result = sp.translate(source='#QCIR-G14\noutput(3)\n2 = exists(1;1)\n3 = and(2,01)\n',
                          language='qcir')
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = public_relation(result)
    comparison = z3.Solver()
    comparison.add(z3.Xor(formula, z3.Bool('01')))
    assert comparison.check() == z3.unsat
