import pytest
import z3

from tools.semantic_checks.public_witness_bijection import prove_public_witness_bijection
from tools.semantic_checks.boolean_structure import structural_equivalence


def checker(a, b):
    proof = structural_equivalence(a, b)
    if proof['equivalent']:
        return dict(proof, solver_queries=0)
    solver = z3.Solver(); solver.add(z3.Xor(a, b))
    return dict(equivalent=solver.check() == z3.unsat, solver_queries=1)


def forms(wrong=False):
    x, y, cost, u, v, r, s = z3.Ints('x y cost u v r s')
    left = z3.And(cost == x + 2*y,
                  z3.Exists(u, z3.And(u >= 0, u <= 2, x == u*u)),
                  z3.Exists(v, z3.And(v >= 1, v <= 3, y == v*v)))
    right = z3.Exists([s, r], z3.And(cost == x + (3 if wrong else 2)*y,
                     s >= 1, s <= 3, y == s*s, r >= 0, r <= 2, x == r*r))
    return left, right


def test_reordered_witnesses_must_pass_complete_body_proof():
    a, b = forms()
    proof = prove_public_witness_bijection(a, b, body_checker=checker)
    assert proof['equivalent'] and proof['witness_count'] == 2
    assert proof['candidate_groups'] == 2
    replay = z3.Solver(); replay.add(z3.Xor(a, b)); assert replay.check() == z3.unsat


def test_shared_incidence_cannot_hide_wrong_ordered_cost():
    a, b = forms(wrong=True)
    assert not prove_public_witness_bijection(a, b, body_checker=checker)['equivalent']
    solver = z3.Solver(); solver.add(z3.Xor(a, b)); assert solver.check() == z3.sat


def test_same_bucket_is_only_a_candidate_not_a_proof():
    x, u, v, r, s = z3.Ints('x u v r s')
    a = z3.Exists([u, v], z3.And(x == u+v, u >= 0, v <= 0))
    b = z3.Exists([r, s], z3.And(x == r+s, r <= 0, s >= 0))
    proof = prove_public_witness_bijection(a, b, body_checker=checker)
    # This heuristic intentionally chooses the wrong order inside one bucket.
    assert proof['equivalent'] is None


@pytest.mark.parametrize('context', ['forall', 'negated', 'disjunction'])
def test_nonpositive_or_universal_contexts_are_not_moved(context):
    x, u, v = z3.Ints('x u v'); p = z3.Bool('p')
    a = z3.Exists(u, z3.And(x == u, u > 0))
    b = {'forall':z3.ForAll(v,z3.And(x==v,v>0)),
         'negated':z3.Not(z3.Exists(v,z3.And(x==v,v>0))),
         'disjunction':z3.Or(p,z3.Exists(v,z3.And(x==v,v>0)))}[context]
    assert not prove_public_witness_bijection(a,b,body_checker=checker)['equivalent']


def test_retyping_or_dropping_public_observation_cannot_match():
    x, u, v = z3.Ints('x u v'); r = z3.Real('r')
    a=z3.Exists(u,z3.And(x==u,u>=0))
    for b in [z3.Exists(r,z3.And(x==r,r>=0)),z3.Exists(v,v>=0)]:
        assert not prove_public_witness_bijection(a,b,body_checker=checker)['equivalent']


def test_unsupported_body_checker_result_is_not_accepted():
    a,b=forms()
    proof=prove_public_witness_bijection(a,b,body_checker=lambda a,b:dict(equivalent=None,solver_queries=0))
    assert proof['equivalent'] is None
