"""Replace private arrays used only through ground reads by scalar witnesses.

For a finite set of distinct literal indices, arbitrary cell values extend to
a total SMT array. Consequently existentially closing the returned witnesses
preserves the complete input relation, including any cost coordinate. This
does not authorize dropping array equalities, symbolic reads, stores, or
unexamined quantified uses. Callers can retain their original formula when
the sufficient syntactic condition below is not met.
"""
from dataclasses import dataclass

import z3


class UnsupportedArrayProjection(ValueError):
    pass


@dataclass(frozen=True)
class GroundArrayProjection:
    body: object
    private_variables: tuple
    eliminated_arrays: tuple
    cells: tuple


def scalarize_ground_array_reads(body, private_variables):
    """Preserve ``Exists(private_variables, body)`` with finite scalar cells.

    Only private arrays with Int indices and non-array values are admitted.
    Every occurrence must be a direct read at a provably constant Int index.
    Repeated reads, including different spellings of the same literal index,
    share a witness. No source-domain assumption or finite array extent is
    needed: indices not read by the complete body are existentially free.
    """
    if not z3.is_bool(body):
        raise UnsupportedArrayProjection("the complete relation must be Boolean")
    private_variables = tuple(private_variables)
    if any(not z3.is_const(v) or v.decl().kind() != z3.Z3_OP_UNINTERPRETED
           for v in private_variables):
        raise UnsupportedArrayProjection("private variables must be constants")
    if any(v.ctx != body.ctx for v in private_variables):
        raise UnsupportedArrayProjection("mixed Z3 contexts")
    if len({v.get_id() for v in private_variables}) != len(private_variables):
        raise UnsupportedArrayProjection("duplicate private variable")
    arrays = {v.get_id(): v for v in private_variables if z3.is_array(v)}
    for array in arrays.values():
        if array.sort().domain().kind() != z3.Z3_INT_SORT:
            raise UnsupportedArrayProjection("private array index is not Int")
        if array.sort().range().kind() == z3.Z3_ARRAY_SORT:
            raise UnsupportedArrayProjection("nested private arrays")
    if not arrays:
        return GroundArrayProjection(body, private_variables, (), ())

    todo, seen, cells, substitutions = [body], set(), {}, []
    while todo:
        term = todo.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_quantifier(term):
            raise UnsupportedArrayProjection("quantified body requires separate proof")
        if term.get_id() in arrays:
            raise UnsupportedArrayProjection("private array used beyond a direct read")
        if z3.is_select(term) and term.arg(0).get_id() in arrays:
            array, index = term.arg(0), z3.simplify(term.arg(1))
            if not z3.is_int_value(index):
                raise UnsupportedArrayProjection("symbolic private array index")
            key = (array.get_id(), index.as_long())
            if key not in cells:
                cells[key] = (array, index, z3.FreshConst(term.sort(), 'array_cell'))
            substitutions.append((term, cells[key][2]))
            # The index simplifier proved a literal independent of all model
            # coordinates. Both the read and its original index disappear.
            continue
        todo.extend(term.children())
    rewritten = z3.substitute(body, *substitutions) if substitutions else body
    witnesses = tuple(v for v in private_variables if v.get_id() not in arrays)
    witnesses += tuple(row[2] for row in cells.values())
    return GroundArrayProjection(rewritten, witnesses, tuple(arrays.values()),
                                 tuple(cells.values()))
