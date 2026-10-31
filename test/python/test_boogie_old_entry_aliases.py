"""Each procedure has its own old-state coordinates, including false VCs."""
import pytest
import somtparser as sp
import z3


CASES = [
    ('independent_entries',
     'var g:int; procedure A() requires g==0; modifies g; ensures g==old(g)+1; {g:=g+1;} '
     'procedure B() requires g==10; modifies g; ensures g==old(g)+1; {g:=g+1;}', True),
    ('later_counterexample',
     'var g:int; procedure A() requires g==0; modifies g; ensures g==old(g)+1; {g:=g+1;} '
     'procedure B() requires g==10; modifies g; ensures g==old(g)+2; {g:=g+1;}', False),
    ('earlier_counterexample',
     'var g:int; procedure A() requires g==0; modifies g; ensures g==old(g)+2; {g:=g+1;} '
     'procedure B() requires g==10; modifies g; ensures g==old(g)+1; {g:=g+1;}', False),
    ('separate_implementations',
     'var g:int; procedure A(); modifies g; ensures g==old(g)+1; '
     'procedure B(); modifies g; ensures g==old(g)+2; '
     'implementation A(){g:=g+1;} implementation B(){g:=g+2;}', True),
    ('call_entry_is_not_procedure_entry',
     'var g:int; procedure Main() requires g==5; modifies g; ensures g==old(g)+2; '
     '{call Bump(); call Bump(); assert g==7;} '
     'procedure Bump() modifies g; ensures g==old(g)+1; {g:=g+1;}', True),
    ('multiple_global_sorts',
     'var g:int; var b:bool; procedure A() modifies g,b; '
     'ensures g==old(g)+1 && b==!old(b); {g:=g+1; b:=!b;} '
     'procedure B() modifies g,b; ensures g==old(g)-1 && b==old(b); {g:=g-1;}', True),
]


@pytest.mark.parametrize('infer', [False, True], ids=['declared-frame', 'inferred-frame'])
@pytest.mark.parametrize('horn', [False, True], ids=['vc', 'horn'])
@pytest.mark.parametrize('name,source,verified', CASES, ids=[row[0] for row in CASES])
def test_old_global_coordinates_preserve_all_procedure_decisions(name, source, verified, horn, infer):
    options = {}
    if horn:
        options['chc'] = '1'
    if infer:
        options['infer_modifies'] = '1'
    result = sp.translate(source=source, language='boogie', options=options)
    assert result.ok, [item.message for item in result.diagnostic_items]
    solver = z3.SolverFor('HORN') if horn else z3.Solver()
    solver.set(timeout=10000)
    solver.from_string(result.to_smt2())
    expected = (z3.sat if verified else z3.unsat) if horn else (z3.unsat if verified else z3.sat)
    assert solver.check() == expected, (name, solver.reason_unknown())
