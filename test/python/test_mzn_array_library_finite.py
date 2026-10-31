"""Finite array library calls preserve values and follow their index contracts."""
from _public_relation import public_relation
import z3
import somtparser as sp


def translated(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, public_relation(result)


def assert_relation_matches(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    expected_expr = z3.BoolVal(expected) if isinstance(expected, bool) else expected
    solver.add(z3.Xor(actual, expected_expr))
    assert solver.check() == z3.unsat


def assert_selector_relation_matches(actual, selector_value, result_value):
    """Compare the full model relation, including selector bounds/constraints."""
    idx = z3.Int("idx")
    expected = z3.And(idx >= 0, idx <= 3, idx == selector_value,
                      z3.BoolVal(result_value))
    assert_relation_matches(actual, expected)


def test_length_counts_rank_one_and_rank_two_cells_and_drives_parameter_initializers():
    source = r"""
array[4..6] of int: costs = array1d(4..6, [3, -2, 4]);
array[-1..0, 5..7] of int: grid = array2d(-1..0, 5..7, [1,2,3,4,5,6]);
int: n = length(costs);
int: total = length(grid);
constraint n = 3 /\ total = 6 /\ sum(i in 1..length(costs))(i) = 6;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_length_ignores_partial_cell_definedness_in_positive_and_negated_relations():
    _, actual = translated("constraint length([1 div 0]) = 1; solve satisfy;")
    assert_relation_matches(actual, True)
    _, negated = translated(
        "constraint not (length([1 div 0]) = 1); solve satisfy;"
    )
    assert_relation_matches(negated, False)


def test_length_retains_undefined_whole_slice_guard():
    source = r"""
array[1..2] of var int: a;
constraint length(a[1 div 0..2]) = 2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, False)


def test_length_retains_partial_cell_guards_added_by_reverse_and_sort():
    cases = (
        ("reverse([1 div 0, 2])", "reverse([1, 2])", 2),
        ("sort([1 div 0, 2])", "sort([1, 2])", 2),
        ("reverse(sort([1 div 0, 2]))", "reverse(sort([1, 2]))", 2),
        ("sort([1 div 0, 2]) ++ [3]", "sort([1, 2]) ++ [3]", 3),
    )
    for expression, defined_expression, expected_length in cases:
        _, actual = translated(
            f"constraint length({expression}) = {expected_length}; solve satisfy;"
        )
        assert_relation_matches(actual, False)
        _, defined = translated(
            f"constraint length({defined_expression}) = {expected_length}; solve satisfy;"
        )
        assert_relation_matches(defined, True)


def test_undefined_whole_slice_guard_survives_concat():
    _, actual = translated(r"""
array[1..2] of var int: a;
constraint length(a[0..2] ++ [5]) = 3;
solve satisfy;
""")
    assert_relation_matches(actual, False)


def test_undefined_whole_slice_guard_survives_reverse():
    _, actual = translated(r"""
array[1..2] of var int: a;
constraint length(reverse(a[0..2])) = 2;
solve satisfy;
""")
    assert_relation_matches(actual, False)


def test_undefined_whole_slice_guard_survives_col():
    _, actual = translated(r"""
array[1..2,1..2] of var int: m;
constraint length(col(m[.., 1 div 0..2], 1)) = 2;
solve satisfy;
""")
    assert_relation_matches(actual, False)


def test_undefined_array_guards_survive_comprehension_and_generator_routes():
    model_prefix = "array[1..2] of int: a = [1, 2]; "
    unsat_sources = (
        "constraint length([i | i in reverse(a[0..2])]) = 2; solve satisfy;",
        "constraint not (length([i | i in reverse(a[0..2])]) = 2); solve satisfy;",
    )
    for suffix in unsat_sources:
        _, actual = translated(model_prefix + suffix)
        assert_relation_matches(actual, False)

    _, defaulted = translated(
        model_prefix
        + "int: n = length([i | i in reverse(a[0..2])]) default 99; "
        + "constraint n = 99; solve satisfy;"
    )
    assert_relation_matches(defaulted, True)


def test_shape_only_length_ignores_partial_scalar_results_from_array_consumers():
    model_prefix = "array[1..2] of int: a = [1, 2]; "
    expressions = (
        "[sum(i in reverse(a[0..2]))(i)]",
        "[sum(reverse(a[0..2]))]",
        "[min(reverse(a[0..2]))]",
    )
    for expression in expressions:
        _, actual = translated(
            model_prefix + f"constraint length({expression}) = 1; solve satisfy;"
        )
        assert_relation_matches(actual, True)


def test_global_cardinality_array_result_carries_items_whole_array_guard():
    source = r"""
include "globals.mzn";
array[1..2] of int: a = [1, 2];
constraint length(global_cardinality(a[0..2], [1, 2])) = 2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, False)

    source = r"""
include "globals.mzn";
array[1..2] of int: a = [1, 2];
constraint length(global_cardinality(a[1..2], [1, 2])) = 2;
solve satisfy;
"""
    _, positive = translated(source)
    assert_relation_matches(positive, True)


def test_undefined_slice_boolean_global_is_refused_in_scalar_contexts():
    source = r"""
include "globals.mzn";
array[1..2] of var int: a;
constraint global_cardinality(a[0..2], [1, 2], [1, 1]);
solve satisfy;
"""
    assert not sp.translate(source=source, language="minizinc").ok

    source = r"""
include "globals.mzn";
array[1..2] of var int: a;
constraint not (global_cardinality(a[0..2], [1, 2], [1, 1]));
solve satisfy;
"""
    assert not sp.translate(source=source, language="minizinc").ok

    source = r"""
include "globals.mzn";
array[1..2] of var int: a;
constraint (global_cardinality(a[0..2], [1, 2], [1, 1]) default true);
solve satisfy;
"""
    assert not sp.translate(source=source, language="minizinc").ok

    source = r"""
include "globals.mzn";
constraint (global_cardinality([1, 1], [1], [0]) default true);
solve satisfy;
"""
    _, defined_false = translated(source)
    assert_relation_matches(defined_false, False)


def test_forall_undefined_generator_source_is_false_even_under_not_or_default():
    model_prefix = "array[1..2] of var int: a; "
    relations = (
        "forall([i > 0 | i in reverse(a[0..2])])",
        "not (forall([i > 0 | i in reverse(a[0..2])]))",
        "(forall([i > 0 | i in reverse(a[0..2])]) default true)",
    )
    for relation in relations:
        _, actual = translated(model_prefix + f"constraint {relation}; solve satisfy;")
        assert_relation_matches(actual, False)


def test_invalid_slice_boolean_global_and_count_are_refused_in_scalar_contexts():
    prefix = 'include "globals.mzn"; array[1..2] of var int: a; '
    expressions = (
        "alldifferent(a[0..2])",
        "not (alldifferent(a[0..2]))",
        "(alldifferent(a[0..2]) default true)",
        "global_cardinality(a[0..2], [1,2], [1,1])",
        "not (global_cardinality(a[0..2], [1,2], [1,1]))",
        "(global_cardinality(a[0..2], [1,2], [1,1]) default true)",
        "(count(a[0..2], 1) default 99) = 99",
    )
    for expression in expressions:
        result = sp.translate(
            source=prefix + f"constraint {expression}; solve satisfy;",
            language="minizinc",
        )
        assert not result.ok


def test_partial_boolean_global_in_boolean_comprehension_closes_to_false():
    source = r"""
include "globals.mzn";
array[1..2] of var int: a;
constraint forall([alldifferent(a[0..2]) | k in 1..1]);
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, False)


def test_alias_initializer_with_invalid_generator_source_is_refused():
    prefix = "array[1..2] of int: a = [1, 2]; any: xs = [i | i in reverse(a[0..2])]; "
    for constraint in ("length(xs) = 2", "not (length(xs) = 2)"):
        result = sp.translate(
            source=prefix + f"constraint {constraint}; solve satisfy;",
            language="minizinc",
        )
        assert not result.ok


def test_alias_initializer_with_defined_generator_source_remains_usable():
    source = r"""
array[1..2] of int: a = [1, 2];
any: xs = [i | i in reverse(a[1..2])];
constraint length(xs) = 2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_partial_cp_global_inputs_are_false_before_negation():
    cases = (
        ("cumulative([1 div 0],[1],[1],1)",
         "cumulative([0],[1],[1],1)"),
        ("diffn([1 div 0],[0],[1],[1])",
         "diffn([0],[0],[1],[1])"),
        ("circuit([1 div 0, 1])", "circuit([2, 1])"),
        ("table([1 div 0], array2d(1..1,1..1,[1]))",
         "table([1], array2d(1..1,1..1,[1]))"),
        ("inverse([1 div 0],[1])", "inverse([1],[1])"),
    )
    for partial, defined in cases:
        _, positive = translated(f"constraint {partial}; solve satisfy;")
        assert_relation_matches(positive, False)
        _, negative = translated(f"constraint not ({partial}); solve satisfy;")
        assert_relation_matches(negative, True)
        _, defined_positive = translated(f"constraint {defined}; solve satisfy;")
        assert_relation_matches(defined_positive, True)
        defined_negative = sp.translate(
            source=f"constraint not ({defined}); solve satisfy;",
            language="minizinc",
        )
        assert defined_negative.ok
        if not defined.startswith("circuit("):
            _, actual = translated(f"constraint not ({defined}); solve satisfy;")
            assert_relation_matches(actual, False)


def test_defined_false_boolean_global_is_not_mistaken_for_undefined_by_default():
    source = ('include "globals.mzn"; '
              "constraint (alldifferent([1, 1]) default true); solve satisfy;")
    _, actual = translated(source)
    assert_relation_matches(actual, False)

    source = ('include "globals.mzn"; '
              "constraint not (alldifferent([1, 1])); solve satisfy;")
    _, negated = translated(source)
    assert_relation_matches(negated, True)

    _, forall_default = translated(
        "constraint (forall([false]) default true); solve satisfy;"
    )
    assert_relation_matches(forall_default, False)


def test_undefined_alldifferent_cell_is_strict_inside_length():
    source = r"""
include "globals.mzn";
array[1..2] of var int: a;
constraint length([alldifferent(a[0..2])]) = 1;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, False)


def test_length_uses_boolean_cell_producer_specific_partiality():
    prefix = 'include "globals.mzn"; array[1..2] of var int: a; '
    cases = (
        ("forall([i > 0 | i in reverse(a[0..2])])", True),
        ("count(a[0..2], 1)", False),
        ("global_cardinality(a[0..2], [1,2], [1,1])", False),
        ("alldifferent(a[0..2])", False),
    )
    for cell, expected in cases:
        _, actual = translated(
            prefix + f"constraint length([{cell}]) = 1; solve satisfy;"
        )
        assert_relation_matches(actual, expected)


def test_exists_generator_source_is_strict_in_scalar_contexts():
    prefix = "array[1..2] of var int: a; "
    expressions = (
        "exists([i > 0 | i in reverse(a[0..2])])",
        "not (exists([i > 0 | i in reverse(a[0..2])]))",
        "(exists([i > 0 | i in reverse(a[0..2])]) default true)",
    )
    for expression in expressions:
        _, actual = translated(prefix + f"constraint {expression}; solve satisfy;")
        assert_relation_matches(actual, False)


def test_nested_generator_source_guards_follow_iteration_reachability():
    prefix = "array[1..2] of var int: a; constraint "
    cases = (
        ("forall(i in 1..2 where false, j in reverse(a[0..2]))(true)", True),
        ("forall(i in 1..2, j in reverse(a[0..2]) where false)(true)", True),
        ("forall(i in 1..0, j in reverse(a[0..2]))(true)", True),
        ("forall(i in 1..2)(forall(j in reverse(a[0..2]))(true))", False),
    )
    for expression, expected in cases:
        _, actual = translated(prefix + expression + "; solve satisfy;")
        assert_relation_matches(actual, expected)


def test_dynamic_alldifferent_selector_partiality_composes_with_not_and_default():
    prefix = ('include "globals.mzn"; array[1..2] of var int: a; '
              'var 0..3: idx; constraint idx=0; constraint ')
    cases = (
        ("alldifferent([a[idx],a[1]])", False),
        ("not (alldifferent([a[idx],a[2]]))", True),
        ("(alldifferent([a[idx],a[2]]) default true)", False),
    )
    for expression, expected in cases:
        _, actual = translated(prefix + expression + "; solve satisfy;")
        assert_selector_relation_matches(actual, 0, expected)

    valid_prefix = ('include "globals.mzn"; array[1..2] of int: a=[1,2]; '
                    'var 0..3: idx; constraint idx=1; constraint ')
    valid_cases = (
        ("alldifferent([a[idx],a[2]])", True),
        ("not (alldifferent([a[idx],a[2]]))", False),
        ("(alldifferent([a[idx],a[2]]) default true)", True),
    )
    for expression, expected in valid_cases:
        _, actual = translated(valid_prefix + expression + "; solve satisfy;")
        assert_selector_relation_matches(actual, 1, expected)


def test_dynamic_global_cardinality_selector_partiality_composes_with_not_and_default():
    invalid_prefix = ('include "globals.mzn"; array[1..2] of var int: a; '
                      'var 0..3: idx; constraint idx=0; constraint ')
    invalid_cases = (
        ("global_cardinality([a[idx]],[1],[1])", False),
        ("not (global_cardinality([a[idx]],[1],[1]))", True),
        ("(global_cardinality([a[idx]],[1],[1]) default true)", False),
    )
    for expression, expected in invalid_cases:
        _, actual = translated(invalid_prefix + expression + "; solve satisfy;")
        assert_selector_relation_matches(actual, 0, expected)

    valid_prefix = ('include "globals.mzn"; array[1..2] of int: a=[1,2]; '
                    'var 0..3: idx; constraint idx=1; constraint ')
    valid_cases = (
        ("global_cardinality([a[idx]],[1],[1])", True),
        ("not (global_cardinality([a[idx]],[1],[1]))", False),
        ("(global_cardinality([a[idx]],[1],[1]) default true)", True),
    )
    for expression, expected in valid_cases:
        _, actual = translated(valid_prefix + expression + "; solve satisfy;")
        assert_selector_relation_matches(actual, 1, expected)

    _, defined_false_default = translated(
        'include "globals.mzn"; '
        'constraint (global_cardinality([1,1],[1],[0]) default true); solve satisfy;'
    )
    assert_relation_matches(defined_false_default, False)


def test_eager_boolean_value_consumers_do_not_turn_evaluation_errors_into_unsat():
    sources = (
        'include "globals.mzn"; array[1..2] of var int: a; '
        'constraint bool2int(alldifferent(a[0..2]))=1; solve satisfy;',
        'include "globals.mzn"; array[1..2] of var int: a; '
        'array[1..1] of var bool: b=[alldifferent(a[0..2])]; '
        'constraint b[1]; solve satisfy;',
    )
    for source in sources:
        result = sp.translate(source=source, language="minizinc")
        assert not result.ok


def test_in_range_constant_reverse_generator_still_has_expected_length():
    source = r"""
array[1..2] of int: a = [1, 2];
constraint length([i | i in reverse(a[1..2])]) = 2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_whole_array_guards_survive_array_rebuilders_inside_length():
    for expression in (
        "array1d(1..2, reverse(a[0..2]))",
        "array2d(1..1, 1..2, reverse(a[0..2]))",
        "global_cardinality(a[0..2], [1, 2])",
    ):
        expected_length = 2
        source = (f"include \"globals.mzn\"; array[1..2] of var int: a; "
                  f"constraint length({expression}) = {expected_length}; solve satisfy;")
        _, actual = translated(source)
        assert_relation_matches(actual, False)


def test_in_range_constant_array_consumers_remain_supported():
    expressions = (
        ("[i | i in reverse(a[1..2])]", 2),
        ("[sum(i in reverse(a[1..2]))(i)]", 1),
        ("[sum(reverse(a[1..2]))]", 1),
        ("[min(reverse(a[1..2]))]", 1),
        ("array1d(1..2, reverse(a[1..2]))", 2),
        ("array2d(1..1, 1..2, reverse(a[1..2]))", 2),
        ("global_cardinality(a[1..2], [1, 2])", 2),
    )
    for expression, expected_length in expressions:
        _, actual = translated(
            f"array[1..2] of int: a = [1, 2]; "
            f"constraint length({expression}) = {expected_length}; solve satisfy;"
        )
        assert_relation_matches(actual, True)


def test_out_of_range_whole_slice_length_is_undefined_but_default_uses_fallback():
    _, undefined_length = translated(
        "array[1..2] of var int: a; "
        "constraint length(a[0..2]) = 3; solve satisfy;"
    )
    assert_relation_matches(undefined_length, False)
    _, defaulted_length = translated(
        "array[1..2] of var int: a; "
        "int: n = length(a[0..2]) default 7; "
        "constraint n = 7; solve satisfy;"
    )
    assert_relation_matches(defaulted_length, True)


def test_length_of_partially_selected_multidimensional_array_is_declined():
    result = sp.translate(
        source=r"""
array[1..2,1..2] of var int: a;
constraint length(a[1 div 0, ..]) = 2;
solve satisfy;
""",
        language="minizinc",
    )
    assert not result.ok


def test_invalid_fixed_scalar_row_selection_stays_an_error_under_not_and_default():
    sources = (
        r"""
array[1..2,1..2] of var int: a;
constraint not (length(a[1 div 0, ..]) = 2);
solve satisfy;
""",
        r"""
array[1..2,1..2] of var int: a;
int: n = length(a[1 div 0, ..]) default 7;
constraint n = 7;
solve satisfy;
""",
    )
    for source in sources:
        result = sp.translate(source=source, language="minizinc")
        assert not result.ok


def test_reverse_sort_and_composition_preserve_non_one_index_set():
    source = r"""
array[-2..1] of int: costs = array1d(-2..1, [3, -1, 3, 0]);
array[-2..1] of int: rev = reverse(costs);
array[1..4] of int: ordered = sort(costs);
array[1..4] of int: back = reverse(sort(costs));
constraint rev[-2] = 0 /\ rev[-1] = 3 /\ rev[0] = -1 /\ rev[1] = 3;
constraint ordered[1] = -1 /\ ordered[2] = 0 /\ ordered[3] = 3 /\ ordered[4] = 3;
constraint back[1] = 3 /\ back[2] = 3 /\ back[3] = 0 /\ back[4] = -1;
constraint index_set(rev) = -2..1 /\ index_set(ordered) = 1..4;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_reverse_and_sort_accept_empty_one_dimensional_arrays():
    source = r"""
array[3..2] of int: a = [];
constraint length(reverse(a)) = 0 /\ length(sort(a)) = 0;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_sort_orders_nominal_enum_values_without_erasing_their_type():
    source = r"""
enum E = {E0, E1, E2};
array[4..6] of E: a = array1d(4..6, [E2, E0, E1]);
array[1..3] of E: s = sort(a);
constraint s[1] = E0 /\ s[2] = E1 /\ s[3] = E2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_array_calls_work_as_generator_sources_and_finite_array_operands():
    source = r"""
array[3..6] of int: costs = array1d(3..6, [3, -1, 3, 0]);
array[1..4] of int: generated = [i | i in reverse(sort(costs))];
array[1..4] of set of int: candidates = [{0, i} | i in reverse(sort(costs))];
constraint generated[1] = 3 /\ generated[2] = 3 /\ generated[3] = 0 /\ generated[4] = -1;
constraint 0 in candidates[1] /\ 3 in candidates[1] /\ not (1 in candidates[1]);
constraint 0 in candidates[2] /\ 3 in candidates[2] /\ not (1 in candidates[2]);
constraint 0 in candidates[3] /\ not (-1 in candidates[3]);
constraint 0 in candidates[4] /\ -1 in candidates[4] /\ not (1 in candidates[4]);
constraint sum(i in reverse(sort(costs)))(i) = 5;
constraint min(sort(costs)) = -1 /\ max(reverse(costs)) = 3;
constraint count(reverse(sort(costs)), 3) = 2;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_sort_order_is_checked_against_independent_fixed_expected_values():
    source = r"""
array[1..5] of int: a = [4, -3, 4, 0, -3];
array[1..5] of int: ordered = sort(a);
array[1..5] of int: backwards = reverse(sort(a));
constraint ordered[1] = -3 /\ ordered[2] = -3 /\ ordered[3] = 0;
constraint ordered[4] = 4 /\ ordered[5] = 4;
constraint backwards[1] = 4 /\ backwards[2] = 4 /\ backwards[3] = 0;
constraint backwards[4] = -3 /\ backwards[5] = -3;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_sort_rejects_assignment_to_an_incompatible_declared_index_set():
    result = sp.translate(
        source=r"""
array[-2..1] of int: a = array1d(-2..1, [4, -3, 4, 0]);
array[-2..1] of int: ordered = sort(a);
solve satisfy;
""",
        language="minizinc",
    )
    assert not result.ok


def test_wrong_reverse_and_sort_results_are_rejected_by_the_translated_relation():
    source = r"""
array[2..4] of int: a = array1d(2..4, [5, -1, 2]);
array[2..4] of int: r = reverse(a);
array[1..3] of int: s = sort(a);
constraint r[2] = 2 /\ s[2] = -1;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, False)


def test_reverse_retains_nominal_enum_element_type():
    source = r"""
enum E = {E0, E1, E2};
array[4..6] of E: colors = array1d(4..6, [E0, E1, E2]);
array[4..6] of E: backwards = reverse(colors);
constraint backwards[4] = E2 /\ backwards[5] = E1 /\ backwards[6] = E0;
solve satisfy;
"""
    _, actual = translated(source)
    assert_relation_matches(actual, True)


def test_reverse_keeps_element_definedness_guard_inside_negation():
    result = sp.translate(
        source="constraint not (count(reverse([1 div 0]), 1) = 0); solve satisfy;",
        language="minizinc",
    )
    assert not result.ok


def test_sort_rejects_decision_valued_or_non_integer_arrays():
    for declaration in (
        "array[1..2] of var int: a;",
        "array[1..2] of float: a = [1.0, 2.0];",
        "array[1..2] of bool: a = [true, false];",
    ):
        result = sp.translate(
            source=declaration + "constraint sum(sort(a)) = 0; solve satisfy;",
            language="minizinc",
        )
        assert not result.ok


def test_partial_boolean_index_closes_inside_not_if_and_forall():
    contexts = {
        "not": "not a[i]",
        "if": "if a[i] then false else true endif",
        "forall": "forall(k in 1..1)(not a[i])",
    }
    for context, expression in contexts.items():
        for index in (0, 1, 2):
            for cell_value in (False, True):
                source = f"""
array[1..1] of var bool: a;
var 0..2: i;
constraint i = {index};
constraint a[1] = {str(cell_value).lower()};
constraint {expression};
solve satisfy;
                """
                _, actual = translated(source)
                i = z3.Int("i")
                a = z3.Array("a", z3.IntSort(), z3.BoolSort())
                selected = z3.And(i >= 1, i <= 1, z3.Select(a, i))
                if context == "if":
                    consumed = z3.If(selected, z3.BoolVal(False), z3.BoolVal(True))
                else:
                    consumed = z3.Not(selected)
                expected_relation = z3.And(
                    i >= 0, i <= 2, i == index,
                    z3.Select(a, 1) == z3.BoolVal(cell_value), consumed,
                )
                equivalence = z3.Solver()
                equivalence.set(timeout=5000)
                equivalence.add(z3.Xor(actual, expected_relation))
                assert equivalence.check() == z3.unsat, (
                    context, index, cell_value
                )

                solver = z3.Solver()
                solver.set(timeout=5000)
                solver.add(actual)
                status = solver.check()
                assert status in (z3.sat, z3.unsat), solver.reason_unknown()
                # An out-of-range Boolean cell is false at the consuming
                # operator. At index 1, each expression holds iff a[1] is false.
                expected = index != 1 or not cell_value
                assert (status == z3.sat) == expected, (
                    context, index, cell_value
                )
