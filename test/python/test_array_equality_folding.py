"""Array equality is extensional; syntax and shallow variable scans cannot decide it."""
import pytest
import z3
import somtparser as sp


CASES = [
    ("symbolic-default", '(declare-const x Int)',
     '(= ((as const (Array Int Int)) (+ x 1)) ((as const (Array Int Int)) 0))'),
    ("symbolic-store-value", '(declare-const x Int)',
     '(= (store ((as const (Array Int Int)) 0) 0 (+ x 1)) ((as const (Array Int Int)) 0))'),
    ("symbolic-store-index", '(declare-const i Int)',
     '(= (store ((as const (Array Int Int)) 0) (+ i 1) 1) (store ((as const (Array Int Int)) 0) 0 1))'),
    ("bool-domain-covered", '',
     '(= (store (store ((as const (Array Bool Bool)) false) false true) true true) ((as const (Array Bool Bool)) true))'),
    ("bool-domain-different", '',
     '(= (store ((as const (Array Bool Bool)) false) true true) ((as const (Array Bool Bool)) true))'),
    ("bv-domain-covered", '',
     '(= (store (store ((as const (Array (_ BitVec 1) Int)) 0) #b0 7) #b1 7) ((as const (Array (_ BitVec 1) Int)) 7))'),
    ("aliased-write-order", '(declare-const i Int)(declare-const j Int)',
     '(= (store (store ((as const (Array Int Int)) 0) i 1) j 2) (store (store ((as const (Array Int Int)) 0) j 2) i 1))'),
    ("aliased-default-overwrite", '(declare-const i Int)(declare-const j Int)',
     '(= (store (store ((as const (Array Int Int)) 0) i 1) j 0) (store ((as const (Array Int Int)) 0) i 1))'),
    ("uf-default", '(declare-fun f (Int) Int)',
     '(= ((as const (Array Int Int)) (f 0)) ((as const (Array Int Int)) 0))'),
    ("nested-default", '(declare-const x Int)',
     '(= ((as const (Array Bool (Array Int Int))) ((as const (Array Int Int)) (+ x 1))) ((as const (Array Bool (Array Int Int))) ((as const (Array Int Int)) 0)))'),
    ("bound-default", '',
     '(forall ((x Int)) (= (= ((as const (Array Int Int)) (+ x 1)) ((as const (Array Int Int)) 0)) (= x (- 1))))'),
    ("mapimp-whole-array", '(declare-const a (Array Bool Bool))(declare-const b (Array Bool Bool))',
     '(=> (= a b) (= (store ((as const (Array Bool Bool)) (=> (select a false) (select b false))) true (=> (select a true) (select b true))) ((as const (Array Bool Bool)) true)))'),
]
@pytest.mark.parametrize('name,declarations,formula', CASES, ids=[row[0] for row in CASES])
def test_array_equality_export_preserves_the_complete_relation(name, declarations, formula):
    source = declarations + '(assert ' + formula + ')(check-sat)'
    translated = sp.translate(source=source, language='smtlib2')
    assert translated.ok, [diagnostic.message for diagnostic in translated.diagnostic_items]
    context = z3.Context()
    reference = z3.And(*z3.parse_smt2_string(source, ctx=context))
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.Xor(reference, actual))
    assert solver.check() == z3.unsat, (name, solver.reason_unknown(), translated.to_smt2())
