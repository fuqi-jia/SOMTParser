"""Three route semantics and composition boundaries; no LLM/network calls."""
from copy import deepcopy
from pathlib import Path
import sys

import pytest
import z3

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'skills/somtparser-nl-smtlib/scripts'))
import ir2smt as bridge

@pytest.mark.parametrize('node,expected', [
    ('|a b|', '|a b|'),
    ([], '()'),
    (['assert', ['=', '|a b|', '"a ""quote""; (x)"']],
     '(assert (= |a b| "a ""quote""; (x)"))'),
    (['f', [], ['g', 'x'], 'y'], '(f () (g x) y)'),
])
def test_sexpr_preserves_tokens_spacing_and_empty_lists(node, expected):
    before = deepcopy(node)
    assert bridge.sexpr(node) == expected
    assert node == before


def test_sexpr_handles_deep_terms_without_changing_recursion_limit():
    depth = 4000
    node = 'x'
    for _ in range(depth):
        node = ['not', node]
    limit = sys.getrecursionlimit()
    assert bridge.sexpr(node) == '(not ' * depth + 'x' + ')' * depth
    assert sys.getrecursionlimit() == limit


def test_sexpr_serializes_every_shared_occurrence_without_mutation():
    node = ['store', 'a', '0', '7']
    root = ['=', node, node]
    assert bridge.sexpr(root) == '(= (store a 0 7) (store a 0 7))'
    assert root[1] is root[2] is node
    assert node == ['store', 'a', '0', '7']


def test_sexpr_rejects_cycles_without_rejecting_shared_nodes():
    node = ['f']
    node.append(node)
    with pytest.raises(ValueError, match='cyclic SMT expression'):
        bridge.sexpr(node)


def test_sexpr_preserves_wide_term_order():
    items = [str(i) for i in range(10000)]
    assert bridge.sexpr(['f', *items]) == '(f ' + ' '.join(items) + ')'


def test_hir_large_data_table_exports_and_preserves_total_lookup():
    source = 'Choose integer index i and return table entry r, or -1 outside the table.'
    raw = hir()
    raw.update(decision='satisfiability', objectives=[], goal=None,
               declarations=[dict(name='i', sort='Int'), dict(name='r', sort='Int')],
               data={'a': list(range(1, 1201))},
               constraints=[dict(span=[0, len(source)],
                                 expr=O('eq', V('r'),
                                        {'data': 'a', 'indices': [V('i')], 'default': L(-1)}))])
    before = deepcopy(raw)
    result = bridge.render(source, raw, route='hir')
    assert result['status'] == 'translated', result.get('diagnostics')
    assert raw == before
    assert result['meta']['solver_executed'] is False
    assert result['code'].count('(check-sat)') == 1
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.from_string(result['code'])
    i, r = z3.Ints('i r')
    for index, expected in [(-1, -1), (0, 1), (600, 601), (1199, 1200), (1200, -1)]:
        solver.push()
        solver.add(i == index, r != expected)
        assert solver.check() == z3.unsat
        solver.pop()


SOURCE = 'Choose an integer x between 4 and 9. Minimize x.'
L = lambda n: {'literal': n, 'sort': 'Int'}
V = lambda n: {'var': n}
O = lambda n, *a: {'op': n, 'args': list(a)}


@pytest.mark.parametrize('route',['hir','smtlib2','hybrid'])
@pytest.mark.parametrize('dialect',['z3','optimathsat','smtlib-pure'])
def test_request_exposes_caller_dialect_to_resource_selection(route, dialect):
    assert bridge.get_request('Choose x.',{},route,dialect=dialect)['dialect']==dialect


def hir():
    return dict(schema='somt-hir-model-v1', language='hir', decision='optimization',
                declarations=[dict(name='x', sort='Int')], functions=[],
                constraints=[dict(expr={'macro':'in_range', 'args':[V('x'),L(4),L(9)]},span=[0,len(SOURCE)])],
                objectives=[dict(sense='minimize',expr=V('x'),span=[0,len(SOURCE)])],
                objective_order='single',goal=None,assumptions=[],unresolved=[])


def direct():
    program='(declare-const x Int) (assert (and (>= x 4) (<= x 9))) (minimize x) (check-sat)'
    return dict(schema='somt-nl-formal-v1',language='smtlib2',decision='optimization',
                program=program,assumptions=[],unresolved=[],links=[dict(span=[0,len(SOURCE)],fragment='(>= x 4)')])


def hybrid(term='(>= x 4)'):
    base=hir()
    base['constraints'][0]['expr']['args'][1]=L(0)
    return dict(schema='somt-nl-hybrid-v1',hir=base,
                smt_constraints=[dict(span=[0,len(SOURCE)],term=term)])


def load(model, route='hir', dialect='z3'):
    before=deepcopy(model)
    result=bridge.render(SOURCE,model,route=route,dialect=dialect)
    assert model==before
    assert result['status']=='translated',result
    assert result['meta']['solver_executed'] is False
    optimizer=z3.Optimize()
    optimizer.from_string(result['code'])
    return result,optimizer


@pytest.mark.parametrize('route,factory',[('hir',hir),('smtlib2',direct),('hybrid',hybrid)])
def test_all_routes_preserve_complete_relation_and_objective(route,factory):
    result,opt=load(factory(),route)
    x=z3.Int('x')
    solver=z3.Solver()
    solver.add(z3.Xor(z3.And(*opt.assertions()),z3.And(x>=4,x<=9)))
    assert solver.check()==z3.unsat
    assert len(opt.objectives())==1
    solver=z3.Solver()
    solver.add(opt.objectives()[0]!=x)
    assert solver.check()==z3.unsat
    assert opt.check()==z3.sat and opt.model()[x].as_long()==4
    assert result['code']==bridge.render(SOURCE,factory(),route=route)['code']
    assert result['meta']['smt_symbol_interface']
    assert result['code'].count('(check-sat)')==1
    assert '(get-model)' not in result['code']


def test_makespan_exact_even_when_maximized():
    raw=hir()
    raw['objectives'][0].update(sense='maximize',expr={'macro':'makespan','args':[[V('x'),L(3)],[L(1),L(2)]]})
    result,opt=load(raw)
    x=z3.Int('x')
    solver=z3.Solver()
    solver.add(z3.And(*opt.assertions()), opt.objectives()[0] != -z3.If(x+3>=3,x+3,3))
    assert solver.check()==z3.unsat
    assert opt.check()==z3.sat and opt.model()[x].as_long()==9


@pytest.mark.parametrize('term',['(>= x 4) (<= x 5)','(assert false)','(declare-const y Bool)'])
def test_hybrid_rejects_command_injection(term):
    with pytest.raises(ValueError):
        bridge.render(SOURCE,hybrid(term),route='hybrid')


@pytest.mark.parametrize('term',['(>= missing 4)','(+ x 1)'])
def test_hybrid_checks_symbols_and_boolean_sort(term):
    result=bridge.render(SOURCE,hybrid(term),route='hybrid')
    assert result['status']=='translation-error' and result['code'] is None


def test_hybrid_constraint_changes_solution_not_just_metadata():
    _,opt=load(hybrid('(>= x 7)'),'hybrid')
    assert opt.check()==z3.sat and opt.model()[z3.Int('x')].as_long()==7


@pytest.mark.parametrize('route,factory',[('hir',hir),('smtlib2',direct),('hybrid',hybrid)])
def test_pure_smt_never_discards_objective(route,factory):
    result=bridge.render(SOURCE,factory(),route=route,dialect='smtlib-pure')
    assert result['status']=='translation-error' and result['code'] is None


def test_validity_negates_goal():
    raw=hir()
    raw.update(decision='validity',objectives=[],goal=dict(expr=O('ge',V('x'),L(4)),span=[0,len(SOURCE)]))
    result,opt=load(raw)
    assert opt.check()==z3.unsat
    assert result['meta']['verdict_polarity']!='preserved'


def test_cardinality_preserves_repeated_positions():
    raw=hir()
    raw['constraints'].append(dict(span=[0,len(SOURCE)],expr={'macro':'exactly','args':[L(2),[O('eq',V('x'),L(5))]*2]}))
    _,opt=load(raw)
    assert opt.check()==z3.sat and opt.model()[z3.Int('x')].as_long()==5


def test_single_optimathsat_objective_is_retained():
    result,_=load(hir(),dialect='optimathsat')
    assert '(minimize x)' in result['code']


def test_hybrid_request_separates_envelope_from_hir_instruction():
    request=bridge.get_request(SOURCE,{},'hybrid')
    assert request['schema']['properties']['schema']['const']=='somt-nl-hybrid-v1'
    assert request['schema']['properties']['hir']['properties']['schema']['const']=='somt-hir-model-v1'
    assert 'hir_instruction' in request


def test_malformed_macro_cannot_emit_partial_code():
    raw=hir()
    raw['objectives'][0]['expr']={'macro':'makespan','args':[]}
    with pytest.raises(ValueError):
        bridge.render(SOURCE,raw)


def test_pilot_checker_rejects_wrong_cost_and_projects_only_auxiliaries():
    from _skill_relation_oracle import cases,check
    task=cases()[0]
    good=task['reference']+' (declare-const aux Int) (assert (= aux (+ x 1)))'
    assert check(good,task)['status']=='equivalent'
    assert check(task['reference'].replace('(minimize x)','(minimize (+ x 1))'),task)['status']=='semantic-mismatch'
    assert check(task['reference'].replace('(<= x 9)','(<= x 8)'),task)['status']=='semantic-mismatch'


def test_hybrid_schema_references_resolve_from_document_root():
    import jsonschema
    request=bridge.get_request(SOURCE,{},'hybrid')
    model=hybrid()
    model['hir']=bridge.expand_macros(model['hir'])
    jsonschema.validate(model,request['schema'])


def test_every_pilot_input_obeys_the_public_context_contract():
    from _skill_relation_oracle import cases
    for task in cases():
        for route in ['hir','smtlib2','hybrid']:
            request=bridge.get_request(task['source'],task['context'],route)
            assert request['context']==task['context']
            assert 'reference' not in request


def test_makespan_macro_avoids_exponential_json_growth():
    import json
    expr={'macro':'makespan','args':[[V('x'),L(i)] for i in range(64)]}
    expanded=bridge.expand_macros(expr)
    assert len(json.dumps(expanded)) < 1000000
    raw=hir()
    raw['objectives'][0]['expr']=expanded
    _,opt=load(raw)
    assert opt.check()==z3.sat
    assert opt.model().eval(opt.objectives()[0]).as_long()==67


@pytest.mark.parametrize('route',['hir','smtlib2','hybrid'])
def test_packaged_scheduling_example_preserves_relation_and_objective(route):
    import json
    from _skill_relation_oracle import check
    directory=Path(__file__).resolve().parents[2]/'skills/somtparser-nl-smtlib/examples/scheduling'
    source=(directory/'problem.txt').read_text()
    result=bridge.render(source,json.loads((directory/(route+'.json')).read_text()),route=route)
    assert result['status']=='translated',result
    reference='(declare-const start_A Int) (declare-const start_B Int) (declare-const start_C Int) '
    reference+='(assert (and (<= 0 start_A) (<= start_A 6) (<= 0 start_B) (<= start_B 6) (<= 0 start_C) (<= start_C 6) '
    reference+='(or (<= (+ start_A 2) start_B) (<= (+ start_B 3) start_A)) '
    reference+='(or (<= (+ start_A 2) start_C) (<= (+ start_C 1) start_A)) '
    reference+='(or (<= (+ start_B 3) start_C) (<= (+ start_C 1) start_B)))) '
    reference+='(define-fun mx ((a Int) (b Int)) Int (ite (>= a b) a b)) '
    reference+='(minimize (mx (mx (+ start_A 2) (+ start_B 3)) (+ start_C 1)))'
    task=dict(reference=reference,observables=dict(start_A='Int',start_B='Int',start_C='Int'))
    assert check(result['code'],task)['status']=='equivalent'


def test_macro_preprocessing_preserves_literal_data_named_macro():
    raw=hir()
    raw['data']={'macro':[1,2,3]}
    result,_=load(raw)
    assert result['ir']['data']==raw['data']
    assert bridge.expand_hir_macros(raw)['data']==raw['data']


@pytest.mark.parametrize('command',['(push 1)','(pop 1)','(reset)','(reset-assertions)','(check-sat-assuming (true))'])
def test_direct_route_does_not_flatten_incremental_query_semantics(command):
    raw=direct()
    raw['program']=raw['program'].replace('(check-sat)',command+' (check-sat)')
    with pytest.raises(ValueError):
        bridge.render(SOURCE,raw,route='smtlib2')


@pytest.mark.parametrize('route',['hir','smtlib2','hybrid'])
def test_compact_request_retains_all_validation_rules(route):
    full=bridge.get_request(SOURCE,{},route)
    compact=bridge.get_request(SOURCE,{},route,request_profile='compact')
    expected=deepcopy(full['schema'])
    schema=expected['properties']['hir'] if route=='hybrid' else expected
    schema.pop('constructor_api',None)
    assert compact['schema']==expected
    assert compact['source']==full['source'] and compact['context']==full['context']
    assert len(bridge.canonical(compact)) < len(bridge.canonical(full))


@pytest.mark.parametrize('route,factory',[('hir',hir),('smtlib2',direct),('hybrid',hybrid)])
def test_exact_source_quote_is_accepted_by_all_three_routes(route,factory):
    raw=factory()
    entries=raw['links'] if route=='smtlib2' else raw['hir']['constraints'] if route=='hybrid' else raw['constraints']
    entries[0]['span']={'quote':SOURCE}
    result,_=load(raw,route)
    assert result['meta']['source_anchor_resolutions'][0]['after']==[0,len(SOURCE)]
    assert entries[0]['span']=={'quote':SOURCE}


def test_native_construction_failure_gets_multiple_located_shape_errors():
    raw=hir()
    del raw['functions']
    raw['declarations'][0]['span']=[0,5]
    result=bridge.render(SOURCE,raw)
    assert result['status']=='translation-error'
    assert {'/functions','/declarations/0/span'} <= {d['pointer'] for d in result['diagnostic_details']}
