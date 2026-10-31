"""Read our finite-set encodings back and independently compare semantics."""
import pytest
import z3
import somtparser as sp


@pytest.mark.parametrize("op,arity", [("and", 2), ("and", 3), ("or", 2), ("or", 3), ("not", 1)])
@pytest.mark.parametrize("index_sort,index", [("Int", "2"), ("Bool", "false")])
def test_boolean_map_parser_and_hir_roundtrips(op, arity, index_sort, index):
    names = ["A", "B", "C"][:arity]
    declarations = "".join(f"(declare-const {name} (Array {index_sort} Bool))" for name in names)
    text = declarations + f"(assert (select ((_ map {op}) {' '.join(names)}) {index}))"
    parser = sp.parse(text)
    dump = parser.dump_smt2()
    assert "(_ map " + op + ")" in dump
    assert sp.parse(dump).dump_smt2() == dump
    translation = sp.translate(source=dump, language="smtlib2")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    emitted = translation.to_smt2(sp.OmtDialect.Z3)
    solver = z3.Solver()
    # Compare with scalar membership, an independent oracle that also
    # covers variadic API normalization to Z3's binary map functions.
    reference = declarations + f"(assert ({op} " + " ".join(
        f"(select {name} {index})" for name in names) + "))"
    solver.add(z3.Xor(z3.And(list(z3.parse_smt2_string(reference))),
                      z3.And(list(z3.parse_smt2_string(emitted)))))
    assert solver.check() == z3.unsat


def test_minizinc_shaped_nested_set_array_self_read():
    source = (
        "(declare-const x (Array Int (Set Int)))"
        "(assert (= (set.inter (select x 0) (set.insert 0 2 (as set.empty (Set Int)))) (select x 0)))"
        "(assert (= (set.card (select x 0)) 1))"
        "(assert (set.member 2 (select x 0)))"
    )
    original = sp.translate(source=source, language="smtlib2")
    assert original.ok
    emitted = original.to_smt2(sp.OmtDialect.Z3)
    assert "(_ map and)" in emitted
    returned = sp.parse(emitted).dump_smt2()
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(list(z3.parse_smt2_string(emitted))),
                      z3.And(list(z3.parse_smt2_string(returned)))))
    assert solver.check() == z3.unsat
