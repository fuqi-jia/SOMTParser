"""Dynamic Set indexes must be covered by every proved source cell."""
import pytest

import somtparser as sp


@pytest.mark.parametrize("cells,upper", [([0, 1], 2), ([0, 2], 2)])
def test_dynamic_index_does_not_borrow_carrier_from_neighboring_cells(cells, upper):
    # First case extends beyond the last proved cell; second leaves an
    # unproved hole inside the index interval. Both admit an unbounded A[i].
    source = "(declare-const A (Array Int (Set Int)))(declare-const i Int)"
    source += f"(assert (and (<= 0 i) (<= i {upper})))"
    for index in cells:
        cell = f"(select A {index})"
        domain = f"(set.singleton {index})"
        source += f"(assert (= {cell} (set.inter {cell} {domain})))"
    source += "(assert (= (set.card (select A i)) 1))"
    translation = sp.translate(source=source, language="smtlib2")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    with pytest.raises(RuntimeError, match="finite support|carrier"):
        translation.to_smt2(sp.OmtDialect.Z3)
