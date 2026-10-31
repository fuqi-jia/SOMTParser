"""Finite Boolean generators preserve bounded scope and per-cell partiality."""
import pytest
import z3
import somtparser as sp


def _translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert "finite-domain-quantifier" not in result.report.to_json()
    target = result.to_smt2(sp.OmtDialect.Z3)
    assertions = z3.parse_smt2_string(target)
    return z3.And(*assertions), target


def _equivalent(source, expanded):
    left, target = _translate(source)
    right, expanded_target = _translate(expanded)
    for first, second in [(left, right), (right, left)]:
        solver = z3.Solver()
        solver.add(first, z3.Not(second))
        assert solver.check() == z3.unsat, solver.reason_unknown()
    return target, expanded_target


@pytest.mark.parametrize("fold", ["forall", "exists"])
@pytest.mark.parametrize("negate", [False, True])
def test_finite_relation_is_equivalent_to_explicit_expansion(fold, negate):
    source = f"""
      set of int: D=-32..31;
      array[D] of var int:x; var int:y;
      constraint {'not ' if negate else ''}{fold}(i in D)(x[i]==y);
      solve satisfy;
    """
    connective = " /\\ " if fold == "forall" else " \\/ "
    cells = connective.join(f"(x[{i}]=y)" for i in range(-32, 32))
    expanded_source = ("set of int:D=-32..31; array[D] of var int:x; var int:y; "
                       f"constraint {'not ' if negate else ''}({cells}); solve satisfy;")
    target, expanded = _equivalent(source, expanded_source)
    assert "(forall " not in target and "(exists " not in target


@pytest.mark.parametrize("fold,negate", [("exists", False), ("exists", True), ("forall", False)])
def test_undefined_boolean_cells_close_inside_each_binding(fold, negate):
    # Three denominator values cover both defined and undefined cells; the
    # independent second domain crosses the former quantifier threshold.
    source = f"""
      set of int:E=-1..1; set of int:D=1..22;
      array[E] of var int:x;
      constraint {'not ' if negate else ''}{fold}(i in E,j in D)(x[i] div i = 1 /\\ j>0);
      solve satisfy;
    """
    _equivalent(source, source.replace("j in D)", "j in D where true)"))


def test_holes_are_not_widened_and_negative_array_origins_are_preserved():
    members = ",".join(map(str, [*range(-40, -8), *range(1, 33)]))
    source = f"""
      set of int:D={{{members}}};
      array[-40..32] of var int:x;
      constraint exists(i in D)(x[i]=0);
      solve satisfy;
    """
    _equivalent(source, source.replace("i in D)", "i in D where true)"))
    formula, _ = _translate(source)
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    solver = z3.Solver(); solver.add(formula)
    solver.add(*(x[i] == (0 if -8 <= i <= 0 else 1) for i in range(-40, 33)))
    assert solver.check() == z3.unsat


def test_grouped_domains_and_multidimensional_indices_are_exact():
    source = """
      set of int:D=-2..5;
      array[D,D] of var int:x; var int:y;
      constraint exists(i,j in D)(x[i,j]=y /\\ i!=j);
      solve satisfy;
    """
    _equivalent(source, source.replace("i,j in D)", "i,j in D where true)"))


def test_outer_fixed_binding_does_not_escape_or_get_shadowed():
    source = """
      set of int:D=1..64; array[D] of var int:x; int:i=999;
      constraint forall(k in 1..2)(let { int:w=k; } in exists(i in D)(x[i]=w));
      constraint i=999;
      solve satisfy;
    """
    _equivalent(source, source.replace("i in D)", "i in D where true)"))


@pytest.mark.parametrize("generator", [
    "exists(i in D where i>2)(x[i]=i)",
    "exists(i in D,j in 1..i)(x[j]=i)",
    "exists(i in D,j=i)(x[j]=i)",
])
def test_filtered_dependent_and_alias_generators_keep_expansion(generator):
    source = f"set of int:D=1..64; array[D] of var int:x; constraint {generator}; solve satisfy;"
    _translate(source)


def test_helpers_and_parameter_initializers_keep_ordinary_evaluation():
    source = """
      set of int:D=1..64; array[D] of var int:x;
      int:fixed=if exists(i in D)(i=17) then 1 else 0 endif;
      predicate hit(var int:v)=exists(i in D)(x[i]=v);
      constraint fixed=1 /\\ hit(3); solve satisfy;
    """
    _translate(source)


def test_empty_domain_preserves_boolean_units():
    source = "set of int:D={}; var int:x; constraint forall(i in D)(x=i) /\\ not exists(i in D)(x=i); solve satisfy;"
    formula, _ = _translate(source)
    solver = z3.Solver(); solver.add(formula)
    assert solver.check() == z3.sat


def test_fixed_out_of_range_coordinates_retain_the_original_error():
    source = "set of int:D=0..64; array[1..64] of var int:x; constraint exists(i in D)(x[i]=0); solve satisfy;"
    for text in [source, source.replace("i in D)", "i in D where true)")]:
        assert not sp.translate(source=text, language="minizinc").ok


def test_parameter_array_reads_with_a_bound_index_use_expansion():
    source = """
      set of int:D=1..64; array[D] of int:p=[i | i in D]; var int:x;
      constraint exists(i in D)(p[i]=x); solve satisfy;
    """
    _translate(source)


def test_outer_existential_let_binder_keeps_its_scope():
    source = """
      set of int:D=1..64; array[D] of var int:x;
      constraint let { var int:value; } in forall(i in D)(x[i]=value);
      solve satisfy;
    """
    _equivalent(source, source.replace("i in D)", "i in D where true)"))


def test_complex_array_elements_keep_the_original_expansion():
    source = """
      set of int:D=1..64; array[D] of var set of 1..2:x;
      constraint exists(i in D)(x[i]=x[1]); solve satisfy;
    """
    _translate(source)


def test_negated_partial_boolean_cell_keeps_local_false_lifting():
    source = """
      set of int:E=-1..1; set of int:D=1..22; array[E] of var int:x;
      constraint exists(i in E,j in D)(not (x[i] div i=1) /\\ j>0); solve satisfy;
    """
    _equivalent(source, source.replace("j in D)", "j in D where true)"))


@pytest.mark.parametrize("fold", ["forall", "exists"])
def test_reified_finite_generator_keeps_exact_boolean_relation(fold):
    source = f"set of int:D=1..64; array[D] of var int:x; var bool:b; constraint b <-> {fold}(i in D)(x[i]=0); solve satisfy;"
    formula, target = _translate(source)
    assert "(forall " not in target and "(exists " not in target
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    terms = [x[i] == 0 for i in range(1, 65)]
    expected = z3.Bool("b") == (z3.And(*terms) if fold == "forall" else z3.Or(*terms))
    solver = z3.Solver(); solver.add(z3.Xor(formula, expected))
    assert solver.check() == z3.unsat
