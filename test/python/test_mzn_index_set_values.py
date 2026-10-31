"""Index-set values preserve source axes across declarations and expressions."""
import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source + '\nsolve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


@pytest.mark.parametrize('rank,axis', [(n, i) for n in range(1, 7) for i in range(n)])
def test_every_axis_preserves_its_domain_in_declarations_folds_and_membership(rank, axis):
    origins = [-3, 0, 5, -8, 12, 20][:rank]
    dims = ','.join(f'{lo}..{lo+1}' for lo in origins)
    fn = 'index_set' if rank == 1 else f'index_set_{axis+1}of{rank}'
    lo = origins[axis]
    formula = translate(fr'''
      array[{dims}] of var 0..9: a;
      set of int: S = {fn}(a);
      array[S] of var 0..9: b;
      var int: q;
      constraint min(S) = {lo} /\ max(S) = {lo+1} /\ card(S) = 2;
      constraint sum(i in {fn}(a))(i) = {2*lo+1};
      constraint index_set(b) = S;
      constraint q in {fn}(a);
    ''')
    q = z3.Int('q')
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Xor(formula, z3.Or(q == lo, q == lo+1)))
    # Array declarations constrain their values as well as q. Fix those
    # independent cells before comparing the membership truth table.
    a, b = [z3.Array(name, z3.IntSort(), z3.IntSort()) for name in ['a', 'b']]
    solver.add(a == z3.K(z3.IntSort(), z3.IntVal(0)),
               b == z3.K(z3.IntSort(), z3.IntVal(0)))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('declaration', [
    'array[1..0,4..6] of int:a = array2d(1..0,4..6,[]);',
    'array[1..0,4..6] of var int:a;',
])
def test_empty_first_axis_does_not_erase_second_axis(declaration):
    formula = translate(declaration + r'''
      set of int:R = index_set_1of2(a);
      set of int:C = index_set_2of2(a);
      constraint card(R)=0 /\ min(C)=4 /\ max(C)=6 /\ card(C)=3;
      constraint forall(i in index_set_1of2(a))(a[i,4]=99);
    ''')
    solver=z3.Solver();solver.add(formula)
    assert solver.check()==z3.sat


def test_string_array_shape_and_array_expression_shape():
    formula = translate(r'''
      array[-2..-1] of string: names = array1d(-2..-1, ["Ada","Lin"]);
      set of int:S = index_set(names);
      set of int:T = index_set_2of2(array2d(-2..-1,7..8,[1,2,3,4]));
      array[index_set(names)] of var 0..1: x;
      constraint min(S)=-2 /\ max(S)=-1 /\ min(T)=7 /\ max(T)=8;
      constraint card(index_set([9,8,7]))=3;
      constraint x[-2]=1 /\ x[-1]=0;
    ''')
    solver=z3.Solver();solver.add(formula)
    assert solver.check()==z3.sat


@pytest.mark.parametrize('function', ['index_set','index_set_1of3','index_set_2of3'])
def test_wrong_array_rank_is_rejected(function):
    result=sp.translate(source=f'array[1..2,4..5] of var int:a; '
        f'set of int:S={function}(a); solve satisfy;',language='minizinc')
    assert not result.ok
    assert any('dimension' in d.message or 'rank' in d.message for d in result.diagnostic_items)


def test_local_array_alias_index_sets_are_independent():
    formula=translate(r'''
      constraint let { array[-2..-1] of int:a=array1d(-2..-1,[1,2]);
                       set of int:S=index_set(a) } in min(S)=-2;
      constraint let { array[4..5] of int:a=array1d(4..5,[1,2]);
                       set of int:S=index_set(a) } in min(S)=4;
    ''')
    solver=z3.Solver();solver.add(formula)
    assert solver.check()==z3.sat


@pytest.mark.parametrize('membership', ['0..0 union S', 'S union 0..0'])
def test_sparse_union_domains_do_not_fill_holes(membership):
    formula=translate(f'''
      set of int:S = {{3,7}};
      array[-1..-1] of var 0..0 union S:a;
      var int:q;
      constraint a[-1]=q;
      constraint q in {membership};
    ''')
    q=z3.Int('q');a=z3.Array('a',z3.IntSort(),z3.IntSort())
    solver=z3.Solver();solver.set(timeout=10000)
    solver.add(a[-1]==q,z3.Xor(formula,z3.Or(q==0,q==3,q==7)))
    assert solver.check()==z3.unsat


def test_local_fixed_arrays_keep_outer_initializer_scope_and_all_scalar_types():
    formula=translate(r'''
      array[2..3] of int:a=array1d(2..3,[7,8]);
      constraint let { array[4..5] of int:a=array1d(4..5,[a[2],a[3]]);
                       array[int] of bool:b=[true,false];
                       array[-1..0] of string:c=array1d(-1..0,["red","blue"]);
                       array[2..3] of set of int:d=array1d(2..3,[{1,3},{}]);
                       array[-2..-1,7..8] of int:m=array2d(-2..-1,7..8,[1,2,3,4]);
                     } in a[4]=7 /\ a[5]=8 /\ b[1] /\ not b[2]
                          /\ c[-1]="red" /\ card(d[2])=2 /\ card(d[3])=0
                          /\ m[-1,8]=4 /\ min(index_set_2of2(m))=7;
      constraint a[2]=7 /\ a[3]=8;
    ''')
    solver=z3.Solver();solver.add(formula)
    assert solver.check()==z3.sat


@pytest.mark.parametrize('item', [
    'array[1..2] of int:a=[1];',
    'array[1..1] of 1..3:a=[4];',
    'array[1..1] of int:a;',
    'array[1..1] of int:a=[q];',
])
def test_local_fixed_arrays_reject_missing_wrong_or_decision_values(item):
    result=sp.translate(source='var int:q; constraint let {'+item+'} in true; solve satisfy;',
                        language='minizinc')
    assert not result.ok


@pytest.mark.parametrize('rank', range(1, 7))
@pytest.mark.parametrize('from_data', [False, True])
def test_inferred_parameter_array_rank_preserves_each_constructor_axis(rank, from_data, tmp_path):
    origins=[-2,4,7,-1,12,20][:rank]
    axes=','.join(f'{lo}..{lo+1}' for lo in origins)
    values=','.join(str(i+11) for i in range(2**rank))
    initializer=f'array{rank}d({axes},[{values}])'
    declaration=f'array[{",".join(["int"]*rank)}] of int:a'
    source=declaration+(';' if from_data else '='+initializer+';')
    for i,lo in enumerate(origins):
        fn='index_set' if rank==1 else f'index_set_{i+1}of{rank}'
        source+=f'constraint min({fn}(a))={lo} /\\ max({fn}(a))={lo+1};'
    source+=f'var int:q; constraint q=a[{",".join(str(lo+1) for lo in origins)}]; solve satisfy;'
    kwargs={}
    if from_data:
        path=tmp_path/'data.dzn';path.write_text('a='+initializer+';')
        kwargs['data']=[str(path)]
    result=sp.translate(source=source,language='minizinc',**kwargs)
    assert result.ok,[d.message for d in result.diagnostic_items]
    formula=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver=z3.Solver();solver.add(z3.Xor(formula,z3.Int('q')==10+2**rank))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('value', ['[|11,12|21,22|]', 'array2d(-1..0,4..5,[11,12,21,22])'])
def test_inferred_local_matrix_retains_shape_and_values(value):
    row,col=(2,2) if value.startswith('[') else (0,5)
    formula=translate(f'var int:q; constraint q=let {{array[int,int] of int:a={value};}} in a[{row},{col}];')
    solver=z3.Solver();solver.add(z3.Xor(formula,z3.Int('q')==22))
    assert solver.check()==z3.unsat


def test_inferred_decision_matrix_keeps_constructor_axes_and_aliases():
    formula=translate('var int:q; array[int,int] of var int:a=array2d(-1..0,4..5,[q,2,3,4]); '
                      'constraint min(index_set_1of2(a))=-1; constraint a[-1,4]=7;')
    solver=z3.Solver();solver.add(formula,z3.Int('q')!=7)
    assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(formula,z3.Int('q')==7)
    assert solver.check()==z3.sat


@pytest.mark.parametrize('typ', ['int','var int'])
@pytest.mark.parametrize('shape,value', [('int,int','[1,2,3,4]'),('int','array2d(1..2,1..2,[1,2,3,4])')])
def test_inferred_array_rank_is_checked(typ,shape,value):
    result=sp.translate(source=f'array[{shape}] of {typ}:a={value}; solve satisfy;',language='minizinc')
    assert not result.ok
    assert any('rank' in d.message for d in result.diagnostic_items)


def test_inferred_empty_matrix_preserves_nonempty_second_axis():
    formula=translate('array[int,int] of int:a=array2d(1..0,4..6,[]); '
                      'constraint card(index_set_1of2(a))=0 /\\ min(index_set_2of2(a))=4 /\\ card(index_set_2of2(a))=3;')
    solver=z3.Solver();solver.add(formula)
    assert solver.check()==z3.sat
