"""Exact bounded expansion checks for finite MiniZinc recursion.

The IHTC helper `min_age_group` recurses while its fixed integer `n`
decreases. Recursive calls must either be fully expanded or make translation
fail at the normal expression-depth limit; this draft never truncates them.
"""
import z3

import somtparser as sp


def _formula(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def _assert_equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_decreasing_fixed_argument_recursion_expands_to_exact_constant():
    recursive = _formula("""
function int: triangular(int: n) =
  if n <= 0 then 0 else n + triangular(n - 1) endif;
int: input_n = 6;
var int: total;
constraint total = triangular(input_n);
solve satisfy;
""")
    total = z3.Int("total")
    solver = z3.Solver()
    solver.add(recursive)
    assert solver.check() == z3.sat
    _assert_equivalent(recursive, total == 21)


def test_ihtc_min_age_group_recursion_matches_fully_expanded_selection():
    shared = """
array[1..4] of var bool: room_has_age_group;
var int: selected;
"""
    recursive = _formula(shared + """
function var int: min_age_group(int: n, var int: fallback) =
  let { int: b = 1 }
  in if n == 1 then
       if room_has_age_group[b] then b else fallback endif
     elseif n == 2 then
       if room_has_age_group[b] then b
       elseif room_has_age_group[b + 1] then b + 1
       else fallback endif
     elseif n == 3 then
       if room_has_age_group[b] then b
       elseif room_has_age_group[b + 1] then b + 1
       elseif room_has_age_group[b + 2] then b + 2
       else fallback endif
     else min_age_group(n - 1,
            if room_has_age_group[b + n - 1]
            then b + n - 1 else fallback endif)
     endif;
constraint selected = min_age_group(4, 5);
solve satisfy;
""")
    expanded = _formula(shared + """
constraint selected =
  if room_has_age_group[1] then 1
  elseif room_has_age_group[2] then 2
  elseif room_has_age_group[3] then 3
  elseif room_has_age_group[4] then 4
  else 5 endif;
solve satisfy;
""")
    for formula in (recursive, expanded):
        solver = z3.Solver()
        solver.add(formula)
        assert solver.check() == z3.sat
    _assert_equivalent(recursive, expanded)


def test_nonterminating_recursion_fails_instead_of_emitting_a_truncated_term():
    result = sp.translate(source="""
function int: loop(int: n) = loop(n);
constraint loop(0) == 0;
solve satisfy;
""", language="minizinc")
    assert not result.ok
    assert any("expression nests more than" in d.message
               for d in result.diagnostic_items)
