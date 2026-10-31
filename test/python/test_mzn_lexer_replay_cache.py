"""Replayed tokens retain source identity, position, and per-call semantics."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _exact(result, expected):
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("forward", [False, True])
def test_replayed_hex_numbers_comments_and_recursive_bindings(forward):
    definition = """
      function int: f(int:n) =
        if n<=0 then 0x1
        else /* skip this body trivia each time */ f(n-1)+n endif;
    """
    call = "constraint x=sum(i in -0x3..0x3)(f(abs(i)));\n"
    source = "var int:x;\n" + (call+definition if forward else definition+call)
    _exact(sp.translate(source=source+"solve satisfy;", language="minizinc"),
           z3.Int("x") == 27)


def test_equal_offsets_in_separate_include_frames_do_not_share_tokens(tmp_path):
    left, right = tmp_path / "left.mzn", tmp_path / "right.mzn"
    # Matching byte offsets and spellings except for the helper name and value.
    left.write_text("function int: f(int:i)=i+0x3;\n", encoding="utf-8")
    right.write_text("function int: g(int:i)=i+0x7;\n", encoding="utf-8")
    source = f'''
      include "{left}"; include "{right}";
      var int:x; var int:y;
      constraint x=sum(i in 1..12)(f(i));
      constraint y=sum(i in 1..12)(g(i));
      solve satisfy;
    '''
    _exact(sp.translate(source=source, language="minizinc"),
           z3.And(z3.Int("x") == 114, z3.Int("y") == 162))


@pytest.mark.parametrize("length", [127, 128, 129, 512])
def test_long_identifiers_fall_back_without_changing_function_bindings(length):
    name = "p" * length
    source = f'''
      function int: f(int:{name})={name}*{name}+1;
      var int:x;
      constraint x=sum(i in 1..7)(f(i));
      solve satisfy;
    '''
    _exact(sp.translate(source=source, language="minizinc"), z3.Int("x") == 147)


@pytest.mark.parametrize("function_first", [False, True])
def test_cache_capacity_is_an_optimization_limit_only(function_first):
    # More than 4096 different token positions, followed by repeated reads.
    numbers = ",".join(str(i) for i in range(1, 2501))
    data = f"array[1..2500] of int:a=[{numbers}];\n"
    function = "function int:f(int:i)=i*3+7;\n"
    source = (function+data if function_first else data+function) + """
      var int:x;
      constraint x=sum(i in 1..9)(f(i))+a[2500];
      solve satisfy;
    """
    _exact(sp.translate(source=source, language="minizinc"), z3.Int("x") == 2698)


@pytest.mark.parametrize("included", [False, True])
def test_replayed_unterminated_comment_keeps_opening_location(tmp_path, included):
    text = "function int:f(int:i)=i+1;\n% ordinary trivia\n  /* missing closer"
    damaged = tmp_path / "damaged.mzn"
    damaged.write_text(text, encoding="utf-8")
    if included:
        model = tmp_path / "model.mzn"
        model.write_text('include "damaged.mzn"; solve satisfy;', encoding="utf-8")
    else:
        model = damaged
    result = sp.translate(path=str(model), language="minizinc")
    assert not result.ok
    errors = [d for d in result.diagnostic_items if "unterminated block comment" in d.message]
    assert errors
    assert any(d.file.endswith("damaged.mzn") and d.line == 3 and d.column == 3
               for d in errors)


@pytest.mark.parametrize("value", [3, 7, -2])
def test_independent_sources_at_equal_positions_do_not_reuse_old_values(value):
    source = f"var int:x; constraint x=sum(i in 1..8)(i+({value})); solve satisfy;"
    _exact(sp.translate(source=source, language="minizinc"),
           z3.Int("x") == 36 + 8*value)


def test_long_string_token_is_preserved_on_replay():
    literal = "r" * 1024
    source = f'''
      string: s="{literal}";
      function bool: f(int:i)=s="{literal}" /\\ i>=0;
      var int:x;
      constraint x=if forall(i in 0..3)(f(i)) then 17 else 19 endif;
      solve satisfy;
    '''
    _exact(sp.translate(source=source, language="minizinc"), z3.Int("x") == 17)
