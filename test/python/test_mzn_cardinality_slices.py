"""Independent relational checks for MiniZinc cardinality and finite slices.

These checks use independent finite assignment oracles, including a size-reduced
official Mondoku model and its objective.
"""
import itertools

import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, z3.And(*z3.parse_smt2_string(result.to_smt2()))


def check_assignment(relation, assumptions, expected):
    solver = z3.Solver()
    solver.set(timeout=3000)
    solver.add(relation, *assumptions)
    assert solver.check() == (z3.sat if expected else z3.unsat)


@pytest.mark.parametrize("closed", [False, True])
def test_global_cardinality_counts_decisions_with_permuted_integer_cover(closed):
    predicate = "global_cardinality_closed" if closed else "global_cardinality"
    _, relation = translate(f"""
array[-2..0] of var int: x;
array[4..5] of int: cover = array1d(4..5, [7, -3]);
array[4..5] of var int: counts;
constraint {predicate}(x, cover, counts);
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    counts = z3.Array("counts", z3.IntSort(), z3.IntSort())

    def assumptions(values, count_values):
        return [x[i] == value for i, value in zip(range(-2, 1), values)] + [
            counts[i] == value for i, value in zip(range(4, 6), count_values)
        ]

    # Cover position, rather than numeric order, determines which count cell
    # belongs to each value: counts[4] counts 7 and counts[5] counts -3.
    check_assignment(relation, assumptions([7, 7, -3], [2, 1]), True)
    check_assignment(relation, assumptions([7, 7, -3], [1, 2]), False)
    # The open predicate leaves 99 unrestricted; the closed predicate forbids it.
    check_assignment(relation, assumptions([7, 99, -3], [1, 1]), not closed)
    check_assignment(relation, assumptions([-3, -3, 7], [1, 2]), True)


# Duplicate cover values are intentionally not specified here: the generic
# reference predicate only exposes a length(x) >= sum(counts) consequence,
# while a Gecode override may impose distinct cover values.


@pytest.mark.parametrize("predicate", ["global_cardinality", "global_cardinality_closed"])
def test_empty_array_forces_each_decision_count_to_zero(predicate):
    _, relation = translate(f"""
array[3..2] of var int: x;
array[-1..0] of int: cover = array1d(-1..0, [12, -8]);
array[-1..0] of var int: counts;
constraint {predicate}(x, cover, counts);
solve satisfy;
""")
    counts = z3.Array("counts", z3.IntSort(), z3.IntSort())
    check_assignment(relation, [counts[-1] == 0, counts[0] == 0], True)
    check_assignment(relation, [counts[-1] == 0, counts[0] == 1], False)


@pytest.mark.parametrize("source", [
    # Same lengths, distinct index sets violate index_sets_agree.
    "array[1..2] of var int: x; array[4..5] of int: cover=array1d(4..5,[1,2]); "
    "array[0..1] of var int: counts; "
    "constraint global_cardinality(x,cover,counts); solve satisfy;",
    # Counts have a different length from cover.
    "array[1..2] of var int: x; array[4..5] of int: cover=array1d(4..5,[1,2]); "
    "array[4..4] of var int: counts; "
    "constraint global_cardinality_closed(x,cover,counts); solve satisfy;",
])
def test_cardinality_rejects_mismatched_cover_and_count_index_sets(source):
    assert not sp.translate(source=source, language="minizinc").ok


def test_set2array_orders_unique_integer_labels_and_counts_empty_labels():
    _, relation = translate("""
array[6..8] of var int: x;
array[1..3] of var int: counts;
constraint global_cardinality(
    x, set2array({9, -2, 4, -2}), counts);
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    counts = z3.Array("counts", z3.IntSort(), z3.IntSort())
    # set2array's increasing unique order is [-2, 4, 9].
    assignments = [
        x[6] == -2, x[7] == 9, x[8] == -2,
        counts[1] == 2, counts[2] == 0, counts[3] == 1,
    ]
    check_assignment(relation, assignments, True)
    check_assignment(relation, assignments[:-3] + [
        counts[1] == 1, counts[2] == 1, counts[3] == 1,
    ], False)


def test_mondoku_style_set_cover_concat_comprehension_and_both_slice_axes():
    _, relation = translate(r"""
int: W = 2;
int: H = 2;
int: C = 2;
set of int: Colors = 1..C;
set of int: Width = 1..W;
set of int: Height = 1..H;
array[Width, Height] of var 1..C: puzzle;
array[Width, Height] of var 0..C: across = array2d(Width, Height, [
    if puzzle[w-1,h] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
array[Width, Height] of var 0..C: down = array2d(Width, Height, [
    if puzzle[w,h-1] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
constraint forall(h in Height) (
    global_cardinality(across[.., h], set2array({0} union Colors),
                       [W-C] ++ [1 | c in Colors]));
constraint forall(w in Width) (
    global_cardinality(down[w, ..], set2array({0} union Colors),
                       [H-C] ++ [1 | c in Colors]));
solve satisfy;
""")
    puzzle = z3.Array("puzzle", z3.IntSort(), z3.IntSort())
    # Independent definition: each row and column of this 2x2 coloring
    # alternates, so both derived marker slices contain one of each color.
    for values in itertools.product((1, 2), repeat=4):
        cells = {(1, 1): values[0], (1, 2): values[1],
                 (2, 1): values[2], (2, 2): values[3]}
        expected = all(cells[(1, h)] != cells[(2, h)] for h in (1, 2)) and all(
            cells[(w, 1)] != cells[(w, 2)] for w in (1, 2)
        )
        flat = {(1, 1): 0, (1, 2): 1, (2, 1): 2, (2, 2): 3}
        check_assignment(relation, [puzzle[flat[i, j]] == value
                                     for (i, j), value in cells.items()], expected)


def test_finite_slice_subranges_and_omitted_endpoints_keep_nonunit_origins():
    _, relation = translate("""
array[-1..0, 4..6] of var int: a;
constraint a[.., 4..5][0, 5] = 17;
constraint a[-1, ..][6] = 23;
constraint a[-1..0, 6][0] = 31;
solve satisfy;
""")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    # Row-major flat indices: (-1,5)->1, (-1,6)->2, (0,5)->4, (0,6)->5.
    check_assignment(relation, [a[4] == 17, a[2] == 23, a[5] == 31], True)
    check_assignment(relation, [a[4] == 18, a[2] == 23, a[5] == 31], False)


@pytest.mark.parametrize("predicate,closed", [
    ("global_cardinality", False),
    ("global_cardinality_low_up", False),
    ("global_cardinality_low_up_closed", True),
])
def test_cardinality_lower_upper_overloads_and_named_aliases(predicate, closed):
    _, relation = translate(f"""
array[-1..1] of var int: x;
array[4..5] of int: cover = array1d(4..5, [7, -3]);
array[4..5] of int: lower = array1d(4..5, [1, 0]);
array[4..5] of int: upper = array1d(4..5, [2, 1]);
constraint {predicate}(x, cover, lower, upper);
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())

    def check(values, expected):
        counts = {label: values.count(label) for label in (7, -3)}
        in_bounds = 1 <= counts[7] <= 2 and 0 <= counts[-3] <= 1
        all_covered = all(value in (7, -3) for value in values)
        check_assignment(relation,
                         [x[i] == value for i, value in zip(range(-1, 2), values)],
                         in_bounds and (all_covered if closed else True))
        assert expected == (in_bounds and (all_covered if closed else True))

    check([7, 7, -3], True)
    check([7, 99, -3], not closed)
    check([7, 7, 7], False)


@pytest.mark.parametrize("predicate", [
    "global_cardinality", "global_cardinality_low_up",
])
def test_negated_cardinality_accepts_a_definite_violation(predicate):
    _, relation = translate(f"""
array[1..2] of var int: x = [1, 1];
array[4..4] of int: cover = array1d(4..4, [1]);
array[4..4] of int: lower = array1d(4..4, [0]);
array[4..4] of int: upper = array1d(4..4, [0]);
constraint not {predicate}(x, cover, lower, upper);
solve satisfy;
""")
    # Both occurrences violate upper[4]=0, so the negated predicate is true.
    solver = z3.Solver()
    solver.add(relation)
    assert solver.check() == z3.sat


def test_reified_cardinality_false_has_no_unconditional_positive_constraint():
    _, relation = translate("""
array[1..2] of var int: x = [1, 1];
array[4..4] of int: cover = array1d(4..4, [1]);
array[4..4] of int: counts = array1d(4..4, [1]);
var bool: holds;
constraint holds <-> global_cardinality(x, cover, counts);
constraint not holds;
solve satisfy;
""")
    holds = z3.Bool("holds")
    solver = z3.Solver()
    solver.add(relation, holds == z3.BoolVal(False))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("predicate,closed", [
    ("global_cardinality", False),
    ("global_cardinality_closed", True),
])
def test_empty_cover_is_vacuous_open_but_restricts_closed(predicate, closed):
    _, relation = translate(f"""
array[1..2] of var int: x;
array[1..0] of int: cover = [];
array[1..0] of int: counts = [];
constraint {predicate}(x, cover, counts);
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    # With no cover labels, the open predicate has no occurrence requirements.
    # The closed predicate requires every element to belong to the empty set.
    check_assignment(relation, [x[1] == 10, x[2] == -4], not closed)


def test_closed_include_whitelist_accepts_the_official_include_name():
    _, relation = translate('''
include "global_cardinality_closed.mzn";
array[1..2] of var int: x = [7, -3];
array[4..5] of int: cover = array1d(4..5, [7, -3]);
array[4..5] of int: counts = array1d(4..5, [1, 1]);
constraint global_cardinality_closed(x, cover, counts);
solve satisfy;
''')
    solver = z3.Solver()
    solver.add(relation)
    assert solver.check() == z3.sat


def test_exclusive_and_omitted_slice_bounds_select_expected_cells():
    _, relation = translate("""
array[-1..1, 4..7] of var int: a;
constraint a[-1..<1, 5..<7][0, 6] = 40;
constraint a[..<1, 5..][0, 7] = 42;
constraint a[0.., ..<6][1, 5] = 44;
solve satisfy;
""")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    # The source has 4 columns and 3 rows, flattened row-major from zero.
    check_assignment(relation, [a[6] == 40, a[7] == 42, a[9] == 44], True)
    check_assignment(relation, [a[6] == 39, a[7] == 42, a[9] == 44], False)


def test_three_dimensional_slices_with_fixed_outer_and_middle_dimensions():
    _, relation = translate("""
array[-1..0, 4..5, 7..8] of var int: a;
constraint a[.., 5, ..][0, 8] = 51;
constraint a[-1, .., 8][4] = 52;
solve satisfy;
""")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    # Flat row-major coordinates: (0,5,8)->7 and (-1,4,8)->1.
    check_assignment(relation, [a[7] == 51, a[1] == 52], True)
    check_assignment(relation, [a[7] == 51, a[1] == 53], False)


@pytest.mark.parametrize("operation", ["sum", "product", "forall", "exists", "alldifferent"])
def test_aggregates_over_named_finite_slices_match_cell_relations(operation):
    boolean = operation in ("forall", "exists")
    symbol = "b" if boolean else "a"
    declaration = ("array[-1..0,4..6] of var bool: b;" if boolean else
                   "array[-1..0,4..6] of var int: a;")
    if operation in ("sum", "product"):
        target = 1 if operation == "sum" else 6
        body = f"constraint {operation}({symbol}[..,5]) = {target};"
    else:
        body = f"constraint {operation}({symbol}[..,5]);"
    _, relation = translate(declaration + body + "solve satisfy;")
    cells = z3.Array(symbol, z3.IntSort(), z3.BoolSort() if boolean else z3.IntSort())
    # The selected slice has source indices -1..0 at column 5. In the named
    # row-major 2x3 array those are flat cells 1 and 4.
    selected = (1, 4)
    values = (False, True) if boolean else (-1, 0, 1, 2, 3)
    for left, right in itertools.product(values, repeat=2):
        if operation == "sum":
            expected = left + right == 1
        elif operation == "product":
            expected = left * right == 6
        elif operation == "forall":
            expected = left and right
        elif operation == "exists":
            expected = left or right
        else:
            expected = left != right
        check_assignment(relation,
                         [cells[selected[0]] == left, cells[selected[1]] == right],
                         bool(expected))


def test_count_over_named_parameter_array_uses_its_finite_shape():
    _, relation = translate("""
array[-2..1] of int: values = array1d(-2..1, [7, -1, 7, 5]);
var int: occurrences;
constraint occurrences = count(values, 7);
solve satisfy;
""")
    occurrences = z3.Int("occurrences")
    check_assignment(relation, [occurrences == 2], True)
    check_assignment(relation, [occurrences != 2], False)


def test_count_over_finite_slice_and_concatenation_matches_occurrences():
    _, relation = translate("""
array[-1..0, 4..6] of var int: a;
var int: occurrences;
constraint occurrences = count(a[..,5] ++ [7, a[0,6]], 7);
solve satisfy;
""")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    occurrences = z3.Int("occurrences")
    # a[..,5] contributes flat cells 1 and 4; the concat appends literal 7
    # and a[0,6] (flat 5). Compute the expected count from those four values.
    for first, second, final in ((5, 7, 7), (0, 0, 0), (7, 7, 0), (7, 5, 7)):
        expected = int(first == 7) + int(second == 7) + 1 + int(final == 7)
        assignment = [a[1] == first, a[4] == second, a[5] == final]
        check_assignment(relation, assignment + [occurrences == expected], True)
        check_assignment(relation, assignment + [occurrences != expected], False)


def test_chained_slice_read_keeps_division_guard_inside_conditional():
    _, relation = translate("""
array[-1..0, 4..5] of var int: a;
var int: quotient = if a[..,5][0] != 0 then 12 div a[..,5][0] else 99 endif;
solve satisfy;
""")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    quotient = z3.Int("quotient")
    # The chained scalar read [0] is the second row at column 5, flat cell 3.
    check_assignment(relation, [a[3] == 3, quotient == 4], True)
    check_assignment(relation, [a[3] == 0, quotient == 99], True)
    check_assignment(relation, [a[3] == 0, quotient == 4], False)


def test_two_argument_global_cardinality_returns_counts_on_cover_index_set():
    _, relation = translate("""
array[-1..1] of var int: x;
array[4..5] of int: cover = array1d(4..5, [7, -3]);
array[4..5] of var int: counts = global_cardinality(x, cover);
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    counts = z3.Array("counts", z3.IntSort(), z3.IntSort())
    assignments = [x[-1] == 7, x[0] == -3, x[1] == 7,
                   counts[4] == 2, counts[5] == 1]
    check_assignment(relation, assignments, True)
    check_assignment(relation, assignments[:-2] + [counts[4] == 1, counts[5] == 2], False)


def test_initialized_local_count_arrays_keep_two_calls_independent_in_let():
    _, relation = translate("""
array[1..3] of var 1..2: left;
array[1..3] of var 1..2: right;
var int: left_spread = let {
    array[int] of var int: counts = global_cardinality(left, [1, 2]);
} in max(counts) - min(counts);
var int: right_spread = let {
    array[int] of var int: counts = global_cardinality(right, [1, 2]);
} in max(counts) - min(counts);
solve satisfy;
""")
    left = z3.Array("left", z3.IntSort(), z3.IntSort())
    right = z3.Array("right", z3.IntSort(), z3.IntSort())
    left_spread = z3.Int("left_spread")
    right_spread = z3.Int("right_spread")
    independent = [left[1] == 1, left[2] == 1, left[3] == 2,
                   right[1] == 2, right[2] == 2, right[3] == 2]
    check_assignment(relation, independent + [left_spread == 1, right_spread == 3], True)
    check_assignment(relation, independent + [left_spread == 3, right_spread == 1], False)


def test_minimum_and_maximum_range_over_concatenated_named_arrays():
    _, relation = translate("""
array[-1..0] of var int: left;
array[4..5] of var int: right;
constraint min(left ++ right) = -2;
constraint max(left ++ right) = 5;
solve satisfy;
""")
    left = z3.Array("left", z3.IntSort(), z3.IntSort())
    right = z3.Array("right", z3.IntSort(), z3.IntSort())
    assignments = [left[-1] == -2, left[0] == 0, right[4] == 1, right[5] == 5]
    check_assignment(relation, assignments, True)
    check_assignment(relation, [left[-1] == -1, left[0] == 0,
                                right[4] == 1, right[5] == 5], False)


def test_one_argument_array1d_flattens_a_named_multidimensional_array():
    _, relation = translate("""
array[4..5, -1..0] of var int: matrix;
array[1..4] of var int: flat = array1d(matrix);
solve satisfy;
""")
    matrix = z3.Array("matrix", z3.IntSort(), z3.IntSort())
    flat = z3.Array("flat", z3.IntSort(), z3.IntSort())
    # Row-major traversal of [4..5,-1..0] maps to flat indices 0..3;
    # array1d's result is indexed from 1.
    pairs = [(0, 1), (1, 2), (2, 3), (3, 4)]
    values = [11, -2, 7, 19]
    same = [matrix[source] == value for (source, _), value in zip(pairs, values)]
    same += [flat[target] == value for (_, target), value in zip(pairs, values)]
    check_assignment(relation, same, True)
    check_assignment(relation, same[:-4] + [flat[1] == 19, flat[2] == -2,
                                             flat[3] == 7, flat[4] == 11], False)


def first_occurrence_precedes(values, predecessor, successor):
    """The successor may occur only after its predecessor's first occurrence."""
    try:
        successor_at = values.index(successor)
    except ValueError:
        return True
    try:
        predecessor_at = values.index(predecessor)
    except ValueError:
        return False
    return predecessor_at < successor_at


@pytest.mark.parametrize("negated", [False, True])
def test_value_precede_chain_set_argument_matches_exhaustive_first_occurrence_oracle(negated):
    negation = "not (" if negated else ""
    close = ")" if negated else ""
    _, relation = translate(f"""
set of int: Colors = {{1, 2}};
array[3..5] of var int: x;
constraint {negation}value_precede_chain(Colors, x){close};
solve satisfy;
""")
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    for values in itertools.product((0, 1, 2, 9), repeat=3):
        expected = first_occurrence_precedes(values, 1, 2)
        if negated:
            expected = not expected
        check_assignment(relation, [x[i] == value for i, value in zip(range(3, 6), values)], expected)


def test_tiny_mondoku_objective_matches_exhaustive_checkerboard_oracle():
    result = sp.translate(source=r"""
int: W = 2;
int: H = 2;
int: C = 2;
set of int: Colors = 1..C;
set of int: Width = 1..W;
set of int: Height = 1..H;
array[Width, Height] of var Colors: puzzle;
array[Width, Height] of var 0..C: across = array2d(Width, Height, [
    if puzzle[w-1,h] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
array[Width, Height] of var 0..C: down = array2d(Width, Height, [
    if puzzle[w,h-1] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
constraint forall(h in Height) (
    global_cardinality(across[..,h], set2array({0} union Colors),
                       [W-C] ++ [1 | c in Colors]));
constraint forall(w in Width) (
    global_cardinality(down[w,..], set2array({0} union Colors),
                       [H-C] ++ [1 | c in Colors]));
array[int] of var int: diff_across = [
    let {
        array[int] of var int: counts = global_cardinality(puzzle[..,h], set2array(Colors));
        var int: minimum = min(counts);
        var int: maximum = max(counts);
    } in maximum - minimum | h in Height];
array[int] of var int: diff_down = [
    let {
        array[int] of var int: counts = global_cardinality(puzzle[w,..], set2array(Colors));
        var int: minimum = min(counts);
        var int: maximum = max(counts);
    } in maximum - minimum | w in Width];
constraint symmetry_breaking_constraint(value_precede_chain(Colors, array1d(puzzle)));
var int: objective = max(diff_across ++ diff_down);
solve minimize objective;
""", language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]

    # Independently enumerate all 16 two-color matrices. The marker counts
    # require adjacent colors to differ in each row and column; the symmetry
    # chain then keeps only sequences whose first 1 precedes their first 2.
    candidates = []
    for values in itertools.product((1, 2), repeat=4):
        cells = {(1, 1): values[0], (1, 2): values[1],
                 (2, 1): values[2], (2, 2): values[3]}
        rows_differ = all(cells[(w, 1)] != cells[(w, 2)] for w in (1, 2))
        columns_differ = all(cells[(1, h)] != cells[(2, h)] for h in (1, 2))
        if not (rows_differ and columns_differ
                and first_occurrence_precedes(values, 1, 2)):
            continue
        spreads = []
        for w in (1, 2):
            line = [cells[(w, h)] for h in (1, 2)]
            spreads.append(max(line.count(1), line.count(2))
                           - min(line.count(1), line.count(2)))
        for h in (1, 2):
            line = [cells[(w, h)] for w in (1, 2)]
            spreads.append(max(line.count(1), line.count(2))
                           - min(line.count(1), line.count(2)))
        candidates.append((values, max(spreads)))

    assert candidates
    expected_optimum = min(score for _, score in candidates)
    optimizer = z3.Optimize()
    optimizer.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert optimizer.check() == z3.sat
    puzzle = z3.Array("puzzle", z3.IntSort(), z3.IntSort())
    objective = z3.Int("objective")
    model = optimizer.model()
    selected = tuple(model.eval(puzzle[i], model_completion=True).as_long() for i in range(4))
    assert (selected, expected_optimum) in candidates
    assert model.eval(objective, model_completion=True).as_long() == expected_optimum
