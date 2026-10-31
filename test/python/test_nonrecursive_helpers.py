import pytest
import z3
from tools.semantic_checks.nonrecursive_helpers import normalize

PREFIX='(declare-const a (Array Int Int))(declare-const k Int)(declare-const x Int)'
BODY='(+ (select a 0) (select a 1) (* k x))'
HELPER='(define-fun-rec h ((p Int)) Int (+ p '+BODY+'))'


def check(actual, expected):
    ctx=z3.Context();a=z3.Optimize(ctx=ctx);a.from_string(actual)
    b=z3.Optimize(ctx=ctx);b.from_string(expected)
    solver=z3.Solver(ctx=ctx);solver.add(z3.Xor(z3.And(*a.assertions()),z3.And(*b.assertions())))
    assert solver.check()==z3.unsat
    assert len(a.objectives())==len(b.objectives())
    for left,right in zip(a.objectives(),b.objectives()):
        solver=z3.Solver(ctx=ctx);solver.add(left!=right);assert solver.check()==z3.unsat


@pytest.mark.parametrize('context',[
 '(assert (> VALUE 0))',
 '(assert (not (> VALUE 0)))',
 '(assert (or (> x 0) (not (and (> VALUE 0) (< k 7)))))',
 '(assert (= x (ite (> VALUE 0) VALUE (- VALUE))))',
 '(assert true)(minimize VALUE)',
 '(assert true)(maximize VALUE)',
 '(assert (not (= VALUE (h k))))(maximize (- VALUE))',
])
def test_full_positive_negative_nested_relation_and_signed_cost(context):
    tail=context.replace('VALUE','(h x)')
    original=(PREFIX+HELPER+tail).encode()
    normalized,receipt=normalize(original)
    expected=PREFIX+context.replace('VALUE','(+ x '+BODY+')').replace('(h k)','(+ k '+BODY+')')
    check(original.decode(),expected);check(normalized.decode(),expected)
    assert len(receipt['edits'])==1
    assert normalized==original.replace(b'define-fun-rec',b'define-fun',1)


@pytest.mark.parametrize('name',['h','|h|'])
def test_true_recursion_rejected(name):
    data=('(define-fun-rec '+name+' ((x Int)) Int (ite (= x 0) 0 ('+name+' (- x 1))))').encode()
    with pytest.raises(ValueError,match='recursive'):normalize(data)


def test_scope_shadow_conservatively_rejected():
    with pytest.raises(ValueError,match='shadowed'):
        normalize(b'(define-fun-rec h ((h Int)) Int h)')


def test_prior_declaration_collision_rejected():
    with pytest.raises(ValueError,match='collision'):
        normalize(b'(declare-fun h (Int) Int)(define-fun-rec h ((x Int)) Int x)')


def test_mutual_recursion_rejected():
    with pytest.raises(ValueError,match='mutually recursive'):
        normalize(b'(define-funs-rec ((a ((x Int)) Int)(b ((x Int)) Int)) ((b x)(a x)))')


def test_identical_text_in_comment_and_string_is_not_rewritten():
    data=b'; define-fun-rec h\n(set-info :source "define-fun-rec h")\n(define-fun-rec |sum helper| ((x Int)) Int (+ x 1))\n(assert (not (= (|sum helper| 3) 5)))\n'
    result,receipt=normalize(data)
    assert len(receipt['edits'])==1
    assert result==data.replace(b'(define-fun-rec |sum helper|',b'(define-fun |sum helper|')
    check(result.decode(),'(assert (not (= 4 5)))')


def test_shared_prior_helper_and_zero_arity_free_dependencies():
    original=(PREFIX+'(define-fun f ((v Int)) Int (+ v k))'
       '(define-fun-rec h ((p Int)) Int (+ (f p) (select a 0)))'
       '(define-fun-rec c () Int (+ (h x) k))'
       '(assert (not (= (h x) (h k))))(minimize c)').encode()
    normalized,receipt=normalize(original)
    expected=PREFIX+'(assert (not (= (+ x k (select a 0)) (+ k k (select a 0)))))(minimize (+ x k (select a 0) k))'
    check(original.decode(),expected);check(normalized.decode(),expected);assert len(receipt['edits'])==2
