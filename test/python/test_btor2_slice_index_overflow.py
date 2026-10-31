"""Source slice indices must be validated before narrowing to HIR indices."""
import pytest
import somtparser as sp


@pytest.mark.parametrize("mode", ["inline", "path"])
@pytest.mark.parametrize("upper,lower,result_width", [
    (4294967296, 4294967296, 1),
    (4294967297, 4294967296, 2),
    (4294967296, 0, 1),
])
def test_unused_slice_indices_do_not_wrap(mode, upper, lower, result_width, tmp_path):
    source = (f"1 sort bitvec 1\n2 sort bitvec 4\n3 sort bitvec {result_width}\n"
              f"4 one 1\n5 input 2 source\n6 slice 3 5 {upper} {lower}\n7 bad 4\n")
    options = dict(language="btor2", profile="bmc", options={"bmc_depth": "1"})
    if mode == "path":
        path = tmp_path / "unused-slice.btor2"
        path.write_text(source)
        result = sp.translate(path=str(path), **options)
    else:
        result = sp.translate(source=source, **options)
    assert not result.ok
    assert any(d.line == 6 and "slice' index exceeds" in d.message for d in result.diagnostic_items)
