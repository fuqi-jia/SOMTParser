"""Geometric counterexamples and support provenance for area certificates."""
import hashlib
import importlib.util
from pathlib import Path
import sys

import pytest
import z3

_path = Path(__file__).resolve().parents[2] / "tools/semantic_checks/rectangle_area_certificate.py"
_spec = importlib.util.spec_from_file_location("rectangle_area_certificate", _path)
_module = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _module
_spec.loader.exec_module(_module)
Rectangle = _module.Rectangle
certify = _module.certify_rectangle_area


def integer(value):
    return z3.IntVal(value)


def rect(x, y, w, h, area):
    return Rectangle(*map(integer, (x, y, w, h)), area)


def check(rectangles, *, width=2, height=1, cost=None):
    return certify([], integer(width * height if cost is None else cost),
                   integer(0), integer(0), integer(width), integer(height), rectangles)


@pytest.mark.parametrize("rectangles,width,height,bound", [
    ([rect(0, 0, 1, 1, 1), rect(1, 0, 1, 1, 1)], 2, 1, 2),
    ([rect(0, 0, 1, 1, 1), rect(0, 1, 1, 1, 1)], 1, 2, 2),
    ([rect(0, 0, 1, 1, 1), rect(2, 0, 1, 1, 1)], 3, 1, 2),
    ([rect(0, 0, 2, 3, 6)], 2, 3, 6),
    ([rect(0, 0, 2, 3, 6), rect(2, 0, 1, 3, 3)], 3, 3, 9),
])
def test_edge_touching_and_unused_region_are_sound(rectangles, width, height, bound):
    result = check(rectangles, width=width, height=height)
    assert result['passed'] and result['lower_bound'] == bound
    assert not result['candidate_assignments_used'] and not result['candidate_cost_used']


@pytest.mark.parametrize("rectangles,width,height,cost", [
    ([rect(0, 0, 1, 1, 1), rect(0, 0, 1, 1, 1)], 2, 1, 2),
    ([rect(0, 0, 2, 2, 4), rect(1, 1, 2, 2, 4)], 3, 3, 9),
    ([rect(-1, 0, 1, 1, 1)], 2, 1, 2),
    ([rect(0, -1, 1, 1, 1)], 2, 1, 2),
    ([rect(2, 0, 1, 1, 1)], 2, 1, 2),
    ([rect(0, 1, 1, 1, 1)], 2, 1, 2),
    ([rect(0, 0, 1, 1, 2)], 2, 1, 2),
    ([rect(0, 0, -1, -1, 1)], 2, 1, 2),
    ([rect(0, 0, 1, 1, 1)], 2, 1, -2),
    ([rect(0, 0, 1, 1, 1)], 2, 1, 1),
    ([rect(0, 0, 1, 1, 1)], -2, 1, -2),
    ([rect(0, 0, 1, 1, 1)], 2, -1, -2),
])
def test_invalid_geometry_or_wrong_objective_never_certifies(rectangles, width, height, cost):
    result = check(rectangles, width=width, height=height, cost=cost)
    assert not result['passed'] and result['lower_bound'] is None
    assert result['unproved_premises']


def test_rotations_have_the_same_area_without_fixing_orientation():
    upright = z3.Bool('upright')
    rectangle = Rectangle(integer(0), integer(0), z3.If(upright, 2, 3), z3.If(upright, 3, 2), 6)
    result = check([rectangle], width=3, height=3)
    assert result['passed'] and result['lower_bound'] == 6
    assert 'upright' in result['query_smt2']


def test_real_coordinate_packing():
    rectangle = Rectangle(z3.RealVal('1/2'), z3.RealVal('1/2'), z3.RealVal('1/2'), z3.RealVal(2), 1)
    result = certify([], z3.RealVal(3), z3.RealVal(0), z3.RealVal(0),
                     z3.RealVal(1), z3.RealVal(3), [rectangle])
    assert result['passed'] and result['lower_bound'] == 1


def test_selected_support_is_from_the_actual_assertions():
    x = z3.Int('x')
    assertions = [x >= 0, x <= 1, z3.Bool('unrelated')]
    rectangle = Rectangle(x, integer(0), integer(1), integer(1), 1)
    args = (assertions, integer(2), integer(0), integer(0), integer(2), integer(1), [rectangle])
    result = certify(*args, support_indices=[0, 1])
    assert result['passed'] and result['original_support_indices'] == [0, 1]
    assert result['original_assertion_count'] == 3
    assert not certify(*args, support_indices=[0])['passed']
    assert not certify(*args, support_indices=[1])['passed']


@pytest.mark.parametrize('indices', [[-1], [1], [True], ['0'], [0, 0]])
def test_support_cannot_inject_or_misindex_hypotheses(indices):
    with pytest.raises(ValueError):
        certify([z3.BoolVal(True)], integer(1), integer(0), integer(0), integer(1), integer(1),
                [rect(0, 0, 1, 1, 1)], support_indices=indices)


@pytest.mark.parametrize('area', [0, -1, True, 1.0])
def test_invalid_claimed_area_is_rejected(area):
    with pytest.raises(ValueError):
        check([rect(0, 0, 1, 1, area)])


def test_empty_rectangle_set_is_rejected():
    with pytest.raises(ValueError):
        check([])


def test_bit_vectors_are_not_geometric_integers():
    with pytest.raises(ValueError):
        check([Rectangle(z3.BitVecVal(0, 8), integer(0), integer(1), integer(1), 1)])


def test_boolean_assertions_required():
    with pytest.raises(ValueError):
        certify([integer(1)], integer(1), integer(0), integer(0), integer(1), integer(1),
                [rect(0, 0, 1, 1, 1)])


def test_mixed_context_is_rejected():
    with pytest.raises(ValueError):
        check([Rectangle(z3.IntVal(0, ctx=z3.Context()), integer(0), integer(1), integer(1), 1)])


def test_replay_query_and_original_fingerprints_are_retained():
    x = z3.Int('x')
    original = [x == 0]
    result = certify(original, integer(1), integer(0), integer(0), integer(1), integer(1),
                     [Rectangle(x, integer(0), integer(1), integer(1), 1)])
    assert result['passed']
    assert hashlib.sha256(result['query_smt2'].encode()).hexdigest() == result['query_sha256']
    assert result['original_assertion_hashes'] == [hashlib.sha256(original[0].sexpr().encode()).hexdigest()]
    replay = z3.Solver()
    replay.from_string(result['query_smt2'])
    assert replay.check() == z3.unsat
