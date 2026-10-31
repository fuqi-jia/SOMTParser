"""Large auxiliary definitions retain exact relations at solver boundaries."""
import json
import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize('kind', ['supports', 'conflicts'])
def test_retained_table_definition_agrees_with_finite_relation(kind):
    size = 193
    tuples = ''.join(f'({i},{(73*i+17)%size})' for i in range(size))
    variables = ''.join(f'<var id="{n}">0..192</var>' for n in ['a','b','c','d'])
    source = (f'<instance format="XCSP3" type="COP"><variables>{variables}'
              '</variables><constraints><group><extension><list>%0 %1</list>'
              f'<{kind}>{tuples}</{kind}></extension><args>a b</args>'
              '<args>c d</args></group></constraints><objectives>'
              '<minimize type="sum"><list>a b c d</list></minimize>'
              '</objectives></instance>')
    result = sp.translate(source=source, language='xcsp3', dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    assert '(define-fun-rec __somt_xcsp_group_' in script
    choices = json.loads(result.report.to_json())['choices']
    assert any(c['strategy'] == 'retained-acyclic-definition' for c in choices)
    assert script == result.to_smt2(sp.OmtDialect.Z3)
    # An independent solver checks both polarities, distinct calls and boundaries.
    context = z3.Context()
    solver = z3.Optimize(ctx=context)
    solver.set(timeout=5000)
    solver.from_string(script)
    for a,c in [(0,1),(96,192),(-1,0),(193,0)]:
        for wrong_first in [0,1]:
            for wrong_second in [0,1]:
                b = ((73*a+17)%size + wrong_first)%size
                d = ((73*c+17)%size + wrong_second)%size
                inside = 0 <= a < size and 0 <= c < size
                relation = (not wrong_first and not wrong_second) if kind == 'supports' else (wrong_first and wrong_second)
                expected = inside and relation
                solver.push()
                values = [a,b,c,d]
                solver.add(*(z3.Int(n, ctx=context)==v for n,v in zip(['a','b','c','d'],values)))
                answer = solver.check()
                assert answer == (z3.sat if expected else z3.unsat), (values,answer)
                if expected:
                    objective = solver.objectives()[0]
                    assert solver.model().eval(objective).as_long() == sum(values)
                solver.pop()
