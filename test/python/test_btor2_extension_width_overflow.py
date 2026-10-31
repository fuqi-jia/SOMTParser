"""Indexed extension widths must not wrap during conversion to unsigned."""
import pytest
import somtparser as sp


@pytest.mark.parametrize('operator', ['uext', 'sext'])
@pytest.mark.parametrize('mode', ['inline', 'path'])
@pytest.mark.parametrize('operand_width,result_width,amount,message', [
    # Before the check, truncating this amount to unsigned produced zero and
    # a seemingly well-typed identity despite the enormous source extension.
    (1, 1, 4294967296, 'extension amount exceeds'),
    # The index itself fits, but adding it to width three used to wrap to two.
    (3, 2, 4294967295, 'extended result exceeds'),
])
def test_unused_extensions_reject_index_and_result_width_overflow(
        operator, mode, operand_width, result_width, amount, message, tmp_path):
    text = (f'1 sort bitvec 1\n2 sort bitvec {operand_width}\n'
            f'3 sort bitvec {result_width}\n4 one 1\n5 input 2 source\n'
            f'6 {operator} 3 5 {amount}\n7 bad 4\n')
    options = dict(language='btor2', profile='bmc', options={'bmc_depth': '1'})
    if mode == 'path':
        path = tmp_path / 'unused-overflow.btor2'
        path.write_text(text)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=text, **options)
    assert not result.ok
    assert any(d.line == 6 and message in d.message for d in result.diagnostic_items)
