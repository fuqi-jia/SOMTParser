"""Full literal-table reconstruction, lexical scope and complete-query controls."""
import hashlib
import itertools

import pytest
import z3

from tools import validate_packed_smt_stream as scanner
from tools.semantic_checks.closed_helpers import retain_closed_helpers
from tools.semantic_checks.finite_table_helpers import (
    _Unsupported, compact_literal_table_module, decode_literal_table,
)
from tools.semantic_checks.source_oracles.xcsp_relation import compare
from tools.semantic_checks.source_oracles.xcsp_source import Source


def number(n):
    return str(n) if n >= 0 else '(- '+str(-n)+')'


def edges(groups):
    return {(a, b) for group in groups for a in group for b in group if a != b}


def body(pairs, a='a', b='b', *, grouped=False):
    if not pairs:
        return 'false'
    if grouped:
        rows = {}
        for x, y in pairs:
            rows.setdefault(x, []).append(y)
        terms = ['(and (= '+a+' '+number(x)+') (or '+
                 ' '.join('(= '+number(y)+' '+b+')' for y in ys)+'))'
                 for x, ys in rows.items()]
    else:
        terms = ['(and (= '+a+' '+number(x)+') (= '+number(y)+' '+b+'))' for x, y in pairs]
    return '(or '+' '.join(terms)+')'


def definition(pairs, *, grouped=False, name='f', params=('a', 'b')):
    return '(define-fun-rec '+name+' (('+params[0]+' Int) ('+params[1]+' Int)) Bool '+body(pairs, *params, grouped=grouped)+')'


def relation(pairs, x, y):
    return z3.Or(*[z3.And(x == a, y == b) for a, b in pairs])


def parse(data, context=None):
    target = z3.Optimize(ctx=context)
    target.from_string(data.decode())
    return target


def equal(a, b):
    solver = z3.Solver(ctx=a.ctx)
    solver.add(z3.Xor(a, b))
    assert solver.check() == z3.unsat


GROUPS = [((0, 1, 2, 3),), ((-100, -3, 17, 999999999999999999999999),),
          ((0, 1, 2, 3), (3, 4, 5, 6)),
          ((0, 1, 2, 3), (4, 5, 6, 7), (0, 4, 8, 12), (1, 5, 9, 13))]


@pytest.mark.parametrize('groups,grouped,duplicate', list(itertools.product(GROUPS, (False, True), (False, True))))
def test_every_tuple_decoded_and_exact_unbounded_integer_relation(groups, grouped, duplicate):
    pairs = edges(groups)
    rows = sorted(pairs) * (2 if duplicate else 1)
    original = ('(declare-const x Int)(declare-const y Int)'+definition(rows, grouped=grouped)+'(assert (f x y))').encode()
    token = list(scanner.tokens(definition(rows, grouped=grouped).encode()))
    assert decode_literal_table(token) == pairs
    compact, record = compact_literal_table_module(original)
    assert record['applied'] and record['helpers'][0]['tuples'] == len(pairs)
    assert record['helpers'][0]['complete_reconstruction_equal']
    target = parse(compact)
    x, y = z3.Ints('x y')
    equal(target.assertions()[0], relation(pairs, x, y))
    # Equality above includes every out-of-domain integer, not just table points.
    solver = z3.Solver(); solver.add(target.assertions()[0], x == 10**50, y == 10**50+1)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('table_body', ['false', '(or false false)', '(and false true)',
                                       '(and (= a 1) (= a 2) (= b 3))'])
def test_empty_table_is_exact_false(table_body):
    original = ('(define-fun-rec f ((a Int)(b Int)) Bool '+table_body+')').encode()
    result, record = compact_literal_table_module(original)
    assert record['applied'] and record['helpers'][0]['tuples'] == 0
    target = parse(result+b'(declare-const x Int)(declare-const y Int)(assert (f x y))')
    equal(target.assertions()[0], z3.BoolVal(False))


@pytest.mark.parametrize('bad', [
    '(define-fun-rec g ((a Int)(b Int)) Bool true)',
    '(define-fun-rec g ((a Int)(b Int)) Bool (= a 0))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (or true (and (= a 1)(= b 2))))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (and (= a captured)(= b 2)))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (g a b))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (f a b))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (and (= (+ a 1) 2)(= b 2)))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (not (= a b)))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (forall ((v Int)) (= a v)))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (and (or (= a 1)(= b 2))(= b 3)))',
    '(define-fun-rec g ((a Bool)(b Int)) Bool (and a (= b 1)))',
    '(define-fun-rec g ((a Int)(b Int)) Int a)',
    '(define-fun-rec g ((a Int)(a Int)) Bool false)',
    '(define-fun-rec f ((a Bool)(b Bool)) Bool (and a b))',
    '(define-fun-rec g ((a Int)) Bool (= a 1))',
    '(define-fun-rec g ((a Int)(b Int)) Bool (ite (= a 1) (= b 2) false))',
    '(define-fun-rec g ((|and| Int)(|or| Int)) Bool (and (= |and| 0)(= |or| 1)))',
])
def test_one_unsupported_definition_keeps_entire_module_byte_for_byte(bad):
    original = (definition(edges(GROUPS[0]))+bad).encode()
    compact, record = compact_literal_table_module(original)
    assert compact == original and record['applied'] is False
    assert record['helpers'] == [] and record['input_sha256'] == record['output_sha256']


@pytest.mark.parametrize('bad', [b'(define-fun-rec)', b'(define-fun-rec f ((a Int)(b Int)) Bool)',
                               b'(define-fun-rec f ((a Int)(b Int)) Bool false',
                               b'(define-fun-rec f ((a Int)(b Int)) Bool false) garbage'])
def test_malformed_definition_is_an_unchanged_fallback(bad):
    compact, record = compact_literal_table_module(bad)
    assert compact == bad and not record['applied']


@pytest.mark.parametrize('extra', [
    '(define-funs-rec ((g ((a Int)(b Int)) Bool)) (false))',
    '(define-sort A () Int)', '(push 1)', '(declare-datatypes () ((Color red blue)))',
])
def test_unsupported_command_keeps_even_accepted_table_unchanged(extra):
    original = (definition(edges(GROUPS[0]))+extra).encode()
    compact, record = compact_literal_table_module(original)
    assert compact == original and not record['applied'] and record['helpers'] == []


def test_let_aliases_intersections_true_and_false_rows_are_completely_decoded():
    pairs = edges(GROUPS[0])
    terms = ['(and true (= a '+str(a)+') (= a '+str(a)+') v'+str(b)+')' for a, b in pairs]
    text = ('(define-fun-rec f ((a Int)(b Int)) Bool (let ('+
            ' '.join('(v'+str(n)+' (= b '+str(n)+'))' for n in range(4))+') (or false '+' '.join(terms)+')))')
    assert decode_literal_table(list(scanner.tokens(text.encode()))) == pairs
    _, record = compact_literal_table_module(text.encode())
    assert record['applied']


@pytest.mark.parametrize('params', [('a', 'b'), ('|first parameter|', '|second;parameter|'),
                                  ('a!1', 'a!2'), ('a!0', 'a!100'), ('|a!1|', '|a!2|'),
                                  ('|ite|', '|let|'), ('|not|', '|>=|'), ('|<=|', '|ite|')])
def test_quoted_and_generated_looking_parameter_names_keep_lexical_scope(params):
    pairs = edges(GROUPS[1])
    original = (definition(pairs, params=params)+'(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    equal(parse(original.replace(b'define-fun-rec', b'define-fun')).assertions()[0],
          relation(pairs, *z3.Ints('x y')))
    compact, record = compact_literal_table_module(original)
    assert record['applied']
    equal(parse(compact).assertions()[0], relation(pairs, *z3.Ints('x y')))


def test_renamed_formals_cannot_capture_same_named_global_coordinates():
    pairs = edges(GROUPS[0])
    original = (definition(pairs, params=('|ite|', '|not|'))+
                '(declare-const __somt_literal_column_0 Int)(declare-const __somt_literal_column_1 Int)'
                '(assert (f __somt_literal_column_0 __somt_literal_column_1))').encode()
    compact, record = compact_literal_table_module(original)
    assert record['applied']
    x, y = z3.Ints('__somt_literal_column_0 __somt_literal_column_1')
    equal(parse(compact).assertions()[0], relation(pairs, x, y))


@pytest.mark.parametrize('groups', GROUPS)
def test_direct_binder_free_render_matches_qualified_clique_relation(groups):
    from tools.semantic_checks.table_cliques import CliqueTable, plan_clique_table
    from tools.semantic_checks.finite_table_helpers import render_clique_table
    pairs = edges(groups)
    families = plan_clique_table(2, [(((a, a),), ((b, b),)) for a, b in pairs])
    assert families is not None
    data = b'(declare-const a!1 Int)(declare-const a!2 Int)(assert '+render_clique_table(families, [b'a!1', b'a!2'])+b')'
    a, b = z3.Ints('a!1 a!2')
    equal(parse(data).assertions()[0], CliqueTable(families).relation([a, b]))


def test_same_context_different_bodies_and_sorts_do_not_alias():
    earlier = []
    for groups in (GROUPS[0], GROUPS[1]):
        pairs = edges(groups)
        raw = (definition(pairs)+'(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
        retained, _ = retain_closed_helpers(raw)
        original = parse(retained)
        compact, record = compact_literal_table_module(retained)
        assert record['applied']
        earlier.append((parse(compact).assertions()[0], original.assertions()[0], pairs))
    raw = b'(define-fun-rec f ((a Bool)(b Bool)) Bool (and a b))(declare-const x Bool)(declare-const y Bool)(assert (f x y))'
    assert compact_literal_table_module(raw)[0] == raw
    for actual, original, pairs in earlier:
        equal(actual, original)
        equal(actual, relation(pairs, *z3.Ints('x y')))


@pytest.mark.parametrize('polarity', [False, True])
def test_all_actual_scopes_retained_and_scope_omission_is_observable(polarity):
    pairs = edges(GROUPS[0]); prefix = definition(pairs)+''.join('(declare-const '+name+' Int)' for name in ('x', 'y', 'z'))
    terms = ['(f x y)', '(f y z)']
    if polarity:
        terms = ['(not '+term+')' for term in terms]
    compact, record = compact_literal_table_module((prefix+''.join('(assert '+term+')' for term in terms)).encode())
    target = parse(compact); assert len(target.assertions()) == 2
    full = z3.And(*target.assertions()); solver = z3.Solver(); solver.add(full)
    assert solver.check() == z3.sat
    for i in range(2):
        solver = z3.Solver(); solver.add(z3.Xor(full, target.assertions()[i]))
        assert solver.check() == z3.sat


def test_quantified_compound_and_repeated_arguments_roundtrip_complete_definition():
    pairs = edges(GROUPS[0])
    raw = (definition(pairs)+'(declare-const x Int)(declare-const y Int)'
           '(assert (exists ((v Int)) (and (f (+ x 1) v) (f v y) (not (f v v)))))').encode()
    retained, _ = retain_closed_helpers(raw); original = parse(retained)
    compact, record = compact_literal_table_module(retained); assert record['applied']
    target = parse(compact); equal(original.assertions()[0], target.assertions()[0])
    solver = z3.Solver(); solver.add(z3.Xor(original.assertions()[0], target.assertions()[0]))
    text = solver.to_smt2(); context = z3.Context(); replay = z3.Solver(ctx=context)
    replay.from_string(text); assert replay.check() == z3.unsat


def test_missing_tuple_is_reconstructed_exactly_and_changes_original_semantics():
    pairs = edges(GROUPS[0]); missing = pairs - {(0, 1)}
    raw = (definition(missing)+'(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    compact, record = compact_literal_table_module(raw)
    assert record['applied'] and record['helpers'][0]['representation'] == 'row-groups'
    equal(parse(compact).assertions()[0], relation(missing, *z3.Ints('x y')))
    # Independently expand the modified table to exhibit the precise lost model.
    x, y = z3.Ints('x y'); solver = z3.Solver()
    solver.add(z3.Xor(relation(pairs, x, y), relation(missing, x, y)))
    assert solver.check() == z3.sat
    assert solver.model().eval(x).as_long() == 0 and solver.model().eval(y).as_long() == 1


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('private', [False, True])
def test_public_compare_archives_original_before_proving_ordered_cost(direction, private):
    pairs = edges(GROUPS[0]); x, y = z3.Ints('x y')
    source = Source({'x': x, 'y': y}, {'x': ((0, 3),), 'y': ((0, 3),)},
                    [z3.And(x >= 0, x <= 3), z3.And(y >= 0, y <= 3), relation(pairs, x, y)],
                    [(direction, x), ('minimize', y+1)], 1, 'COP')
    # A real private witness keeps this control on the complete-joint path,
    # so it exercises table compaction even when scalar costs match directly.
    raw = ('(declare-const x Int)(declare-const y Int)'+
           ('(declare-const unused Bool)' if private else '')+definition(pairs)+
           '(assert (and (>= x 0)(<= x 3)))(assert (and (>= y 0)(<= y 3)))'
           '(assert (f x y))('+direction+' x)(minimize (+ y 1))(check-sat)(exit)').encode()
    archived = []
    def callback(left, right):
        solver = z3.Solver(); solver.add(z3.Xor(left, right)); text = solver.to_smt2()
        assert 'define-funs-rec' in text or 'define-fun-rec' in text
        archived.append(hashlib.sha256(text.encode()).hexdigest())
        context = z3.Context(); replay = z3.Solver(ctx=context); replay.from_string(text)
        assert replay.check() == z3.unsat
    result = compare(source, raw, solve=True, project_private_scalars=True, complete_relation_callback=callback)
    assert result['equivalent'] and result['signed_cost_equal'] and len(archived) == 1
    if private:
        assert result['literal_table_helpers']['applied']
    else:
        assert result['domain_cost_certificate']['equivalent'] is True
        assert result['composed_feasibility_certificate']['equivalent'] is True


def test_helper_free_target_never_retains_or_rescans_full_module(monkeypatch):
    from tools.semantic_checks.source_oracles import xcsp_relation
    x = z3.Int('x')
    source = Source({'x': x}, {'x': ((0, 3),)}, [z3.And(x >= 0, x <= 3)], [], 0, 'CSP')
    data = b'(declare-const x Int)(assert (and (>= x 0)(<= x 3)))(check-sat)(exit)'
    target = xcsp_relation.target_model(data, source)
    assert target._somt_complete_module is None
    def forbidden(*args):
        raise AssertionError('helper-free module was scanned again')
    monkeypatch.setattr(xcsp_relation, 'compact_literal_table_module', forbidden)
    result = compare(source, data, solve=True)
    assert result['equivalent'] and not result['literal_table_helpers']['applied']


def test_reparse_failure_returns_to_original_relation_and_records_attempt(monkeypatch):
    pairs = edges(GROUPS[0]); x, y = z3.Ints('x y')
    source = Source({'x': x, 'y': y}, {'x': ((0, 3),), 'y': ((0, 3),)},
                    [relation(pairs, x, y)], [], 1, 'CSP')
    data = ('(declare-const x Int)(declare-const y Int)'+definition(pairs)+'(assert (f x y))(check-sat)(exit)').encode()
    original_parse = z3.Optimize.from_string
    def fail_compact(self, text):
        if '( define-fun ' in text:
            raise z3.Z3Exception('controlled compact parse failure')
        return original_parse(self, text)
    monkeypatch.setattr(z3.Optimize, 'from_string', fail_compact)
    result = compare(source, data, solve=True)
    record = result['literal_table_helpers']
    assert result['equivalent'] and not record['applied']
    assert record['output_sha256'] == record['input_sha256']
    assert record['attempted_output_sha256'] != record['input_sha256']


@pytest.mark.parametrize('offset', [-10**30, -2, 100000000000000000000])
@pytest.mark.parametrize('style', ['inclusive', 'reversed', 'strict', 'intersect'])
def test_complete_finite_literal_intervals_decode_every_endpoint(offset, style):
    points = list(range(offset, offset+4)); pairs = edges([points])
    def interval(lo, hi):
        if style == 'inclusive':
            return '(and (>= b '+number(lo)+') (<= b '+number(hi)+'))'
        if style == 'reversed':
            return '(and (<= '+number(lo)+' b) (>= '+number(hi)+' b))'
        if style == 'strict':
            return '(and (< '+number(lo-1)+' b) (> '+number(hi+1)+' b))'
        return '(and (>= b '+number(lo-1)+') (> b '+number(lo-1)+') (<= b '+number(hi)+'))'
    rows = ['(and (= a '+number(a)+') (or '+interval(offset, a-1)+' '+interval(a+1, offset+3)+'))' for a in points]
    text = '(define-fun-rec f ((a Int)(b Int)) Bool (or '+' '.join(rows)+'))'
    assert decode_literal_table(list(scanner.tokens(text.encode()))) == pairs
    compact, record = compact_literal_table_module((text+'(declare-const x Int)(declare-const y Int)(assert (f x y))').encode())
    assert record['applied']
    equal(parse(compact).assertions()[0], relation(pairs, *z3.Ints('x y')))


@pytest.mark.parametrize('expression', [
    '(and (= a 1)(>= b 0))', '(and (= a 1)(<= b 0))',
    '(and (= a 1)(or (<= b 0)(>= b 2)))',
    '(and (= a 1)(or true (and (>= b 0)(<= b 3))))',
])
def test_missing_literal_interval_endpoint_is_never_treated_as_a_finite_table(expression):
    raw = ('(define-fun-rec f ((a Int)(b Int)) Bool '+expression+')').encode()
    compact, record = compact_literal_table_module(raw)
    assert compact == raw and not record['applied']


@pytest.mark.parametrize('expression', [
    '(and (= a 1)(>= b 5)(<= b 4))',
    '(and (= a 1)(> b 4)(< b 5))',
    '(and (= a 1)(or (and (>= b 5)(<= b 4)) false))',
    '(and (= a 1)(or (>= b 0)(<= b 3)) (> b 5)(< b 5))',
])
def test_empty_literal_interval_conjunction_is_exact_false(expression):
    raw = ('(define-fun-rec f ((a Int)(b Int)) Bool '+expression+')').encode()
    assert decode_literal_table(list(scanner.tokens(raw))) == set()
    compact, record = compact_literal_table_module(raw)
    assert record['applied'] and record['helpers'][0]['tuples'] == 0
    equal(parse(compact+b'(declare-const x Int)(declare-const y Int)(assert (f x y))').assertions()[0], z3.BoolVal(False))


def test_row_conjunction_intersects_half_intervals_before_finite_enumeration():
    raw = b'(define-fun-rec f ((a Int)(b Int)) Bool (and (>= a (- 2))(<= a 1)(>= b 3)(<= b 5)))'
    assert decode_literal_table(list(scanner.tokens(raw))) == set(itertools.product(range(-2, 2), range(3, 6)))
    compact, record = compact_literal_table_module(raw)
    assert record['applied'] and record['helpers'][0]['representation'] == 'row-groups'
    target = parse(compact+b'(declare-const x Int)(declare-const y Int)(assert (f x y))')
    equal(target.assertions()[0], relation(set(itertools.product(range(-2, 2), range(3, 6))),
                                         *z3.Ints('x y')))
