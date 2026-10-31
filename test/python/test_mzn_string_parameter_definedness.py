"""A literal value does not make a partially defined string a parameter."""
import pytest
import somtparser as sp


@pytest.mark.parametrize('expression', ['a[i]', 'concat([a[i]])'])
def test_dynamic_index_guard_survives_string_parameter_extraction(expression):
    # With a singleton array the value folds to "a", but its index guard
    # remains dynamic. Discarding that guard used to accept i=0 as SAT.
    source = ('array[1..1] of string:a=["a"]; var 0..1:i; '
              f'string:block={expression}; constraint i=0; solve satisfy;')
    result = sp.translate(source=source, language='minizinc')
    assert not result.ok
    assert any('conditionally defined' in d.message for d in result.diagnostic_items)
