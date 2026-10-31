"""Focused SyGuS String grammar tests; remote Z3 qualification is pending."""
from pathlib import Path

import z3
import somtparser as sp


TEST_ROOT = Path(__file__).resolve().parents[2]
ROOT = TEST_ROOT if (TEST_ROOT / "languages/sygus").exists() else TEST_ROOT / "source"
OFFICIAL = ROOT / "languages/sygus/instances/ok/pbe-slia-11604909.sl"


def translate(source, depth=1):
    return sp.translate(source=source, language="sygus", profile="bmc",
                        options={"grammar_depth": str(depth)})


def check_z3(translated):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    return solver.check()


def check_explicit_string_function_witness(translated, use_first_argument):
    """Instantiate a concrete function interpretation in the emitted formula.

    Quantified String function synthesis can be incomplete in Z3. Substituting
    an explicit interpretation and enumerating the two grammar selectors gives
    a witness for this *actual target*, including all generated equations and
    the original examples. No assertion is dropped or rebuilt by this test.
    """
    formula = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    declarations = {}
    pending = [formula]
    while pending:
        expr = pending.pop()
        if z3.is_quantifier(expr):
            pending.append(expr.body())
        elif z3.is_app(expr):
            if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                declarations[str(expr.decl().name())] = expr.decl()
            pending.extend(expr.children())
    function = declarations["__somt_sygus_function_0"]
    guard = declarations["__somt_sygus_function_1"]
    selectors = [declarations[name]() for name in sorted(declarations)
                 if name.startswith("__somt_sygus_candidate_0_")]
    guard_selectors = [declarations[name]() for name in sorted(declarations)
                      if name.startswith("__somt_sygus_candidate_1_")]
    assert function.arity() == 2 and guard.arity() == 0
    assert len(selectors) == 2 and len(guard_selectors) == 1
    interpreted = z3.substitute_funs(
        formula, (function, z3.Var(0 if use_first_argument else 1,
                                   z3.StringSort())))
    outcomes = []
    for selected in range(2):
        fixed = z3.substitute(interpreted,
            (guard(), z3.BoolVal(True)),
            (guard_selectors[0], z3.BoolVal(True)),
            *[(selector, z3.BoolVal(i == selected))
              for i, selector in enumerate(selectors)])
        solver = z3.Solver()
        solver.set(timeout=5000)
        solver.add(z3.simplify(fixed))
        outcomes.append(solver.check())
    return outcomes


def test_pinned_official_pbe_slia_grammar_translates_and_z3_parses():
    translated = translate(OFFICIAL.read_text(encoding="utf-8"))
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.report.fidelity.sound
    assert not translated.report.fidelity.complete
    script = translated.to_smt2()
    # SyGuS 2.1 legacy spellings are normalized only in the target SMT term.
    assert "int.to.str" not in script
    assert "str.to.int" not in script
    assert z3.parse_smt2_string(script) is not None


def test_escaped_quotes_and_unicode_strings_are_preserved_for_z3():
    source = r'''(set-logic SLIA)
(synth-fun f () String ((Start String ("a""b" "\u{3bb}"))))
(constraint (= f "a""b"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_quoted_symbols_remain_single_identifiers():
    source = r'''(set-logic SLIA)
(synth-fun |f odd| ((|x odd| String)) String
  ((Start String ((Variable String)))))
(synth-fun g () Bool ((StartB Bool (true))))
(constraint (= (|f odd| "hello") "hello"))
(constraint g)
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert "|x odd|" in translated.to_smt2()
    assert check_z3(translated) == z3.sat


def test_empty_and_quote_bearing_identifiers_round_trip_through_variable_grammar():
    source = r'''(set-logic SLIA)
(synth-fun || ((|x"y| String) (|true| String)) String
  ((Start String ((Variable String)))))
(synth-fun g () Bool ((StartB Bool (true))))
(constraint (= (|| "hello" "world") "hello"))
(constraint g)
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert '|x"y|' in script
    # The shared lowerer alpha-renames builtin spellings. Inspect the parsed
    # binders so this String parameter cannot become the Bool literal true.
    formulas = z3.parse_smt2_string(script)
    pending = list(formulas)
    parameters = []
    while pending:
        expression = pending.pop()
        if z3.is_quantifier(expression):
            parameters.append([(str(expression.var_name(i)),
                                str(expression.var_sort(i)))
                               for i in range(expression.num_vars())])
            pending.append(expression.body())
        elif z3.is_app(expression):
            pending.extend(expression.children())
    assert [('x"y', "String"), ("true!0", "String")] in parameters
    assert sorted(map(str, check_explicit_string_function_witness(translated, True))) == ["sat", "unsat"]
    assert check_explicit_string_function_witness(translated, False) == [z3.unsat, z3.unsat]


def test_string_operators_in_grammar_and_constraints_are_typed_and_parsed():
    source = r'''(set-logic SLIA)
(synth-fun f ((s String)) String ((Start String (s (str.++ s "x")))) )
(constraint (let ((joined (str.++ "a" "b"))) (= joined "ab")))
(constraint (str.contains "abc" "b"))
(constraint (str.prefixof "a" "abc"))
(constraint (str.suffixof "c" "abc"))
(constraint (= (str.len "abc") 3))
(constraint (= (str.to_int "12") 12))
(constraint (= (str.from_int 12) "12"))
(constraint (= (str.indexof "abc" "b" 0) 1))
(constraint (= (str.at "abc" 1) "b"))
(constraint (= (str.substr "abc" 1 1) "b"))
(constraint (= (str.replace "abc" "b" "x") "axc"))
(check-synth)'''
    translated = translate(source)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_legacy_string_conversion_operators_preserve_candidate_semantics():
    to_string = r'''(set-logic SLIA)
(synth-fun f ((i Int)) String ((Start String ((int.to.str i)))))
(constraint (= (f 12) "12"))
(check-synth)'''
    translated = translate(to_string, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert "int.to.str" not in script
    assert check_z3(translated) == z3.sat

    contradictory = to_string.replace('"12"', '"13"')
    translated_bad = translate(contradictory, depth=0)
    assert translated_bad.ok, [d.message for d in translated_bad.diagnostic_items]
    assert check_z3(translated_bad) == z3.unsat

    to_int = r'''(set-logic SLIA)
(synth-fun g ((s String)) Int ((Start Int ((str.to.int s)))))
(constraint (= (g "12") 12))
(check-synth)'''
    translated = translate(to_int, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert "str.to.int" not in script
    assert check_z3(translated) == z3.sat

    contradictory = to_int.replace('12))', '13))')
    translated_bad = translate(contradictory, depth=0)
    assert translated_bad.ok, [d.message for d in translated_bad.diagnostic_items]
    assert check_z3(translated_bad) == z3.unsat


def test_joint_candidates_normalize_legacy_string_conversion_operators():
    source = r'''(set-logic SLIA)
(synth-fun f ((i Int)) String ((StartS String ((int.to.str i)))))
(synth-fun g ((s String)) Int ((StartI Int ((str.to.int s)))))
(constraint (= (f 12) "12"))
(constraint (= (g "34") 34))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert "str.from_int" in script
    assert "str.to_int" in script
    assert "int.to.str" not in script
    assert "str.to.int" not in script
    assert check_z3(translated) == z3.sat


def test_user_helper_named_like_legacy_alias_is_not_rewritten_in_all_logic():
    source = r'''(set-logic ALL)
(define-fun int.to.str ((i Int)) String "manual")
(synth-fun f ((i Int)) String ((Start String ((int.to.str i)))))
(constraint (= (f 1) "manual"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert "str.from_int" not in script
    assert "int.to.str" not in script
    assert '"manual"' in script
    assert check_z3(translated) == z3.sat


def test_user_helper_named_like_reverse_legacy_alias_is_not_rewritten_in_all_logic():
    source = r'''(set-logic ALL)
(define-fun str.to.int ((s String)) Int 7)
(synth-fun f ((s String)) Int ((Start Int ((str.to.int s)))))
(constraint (= (f "anything") 7))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert "str.to.int" not in script
    assert "str.to_int" not in script
    assert check_z3(translated) == z3.sat


def test_fixed_string_candidate_is_unsat_for_conflicting_example():
    source = r'''(set-logic SLIA)
(synth-fun f () String ((Start String ("right"))))
(constraint (= f "wrong"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.unsat


def test_string_grammar_rejects_wrong_operator_argument_sorts():
    source = r'''(set-logic SLIA)
(synth-fun f ((s String)) String ((Start String ((str.at s "0")))))
(constraint (= (f "x") "x"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert not translated.ok
    assert any("str.at requires (String, Int)" in d.message
               or "grammar str.at" in d.message
               for d in translated.diagnostic_items)


def test_quoted_symbol_rejects_forbidden_backslash():
    source = r'''(set-logic SLIA)
(synth-fun |bad\name| () String ((Start String ("x"))))
(check-synth)'''
    translated = translate(source, depth=0)
    assert not translated.ok
    assert any("invalid character in SMT-LIB quoted symbol" in d.message
               for d in translated.diagnostic_items)


def test_quoted_symbols_allow_tab_and_newline_whitespace():
    source = '''(set-logic SLIA)
(synth-fun f ((|line\nname| String) (|tab\tname| String)) String
  ((Start String ((Variable String)))))
(constraint (= (f "x" "x") "x"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_string_literal_does_not_alias_same_named_parameter_during_instantiation():
    source = r'''(set-logic SLIA)
(synth-fun f ((|"p"| String)) String ((Start String ("p"))))
(constraint (= (f "other") "p"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_string_literal_does_not_alias_unused_same_named_global():
    source = r'''(set-logic SLIA)
(declare-var |"g"| String)
(synth-fun f () String ((Start String ("g"))))
(constraint (= (str.len f) 1))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_string_literal_matching_helper_name_is_not_a_recursive_reference():
    source = r'''(set-logic SLIA)
(define-fun |"h"| ((s String)) String "h")
(synth-fun f ((x String)) String ((Start String (x))))
(constraint (= (f "h") (|"h"| "right")))
(constraint (= (|"h"| "other") "h"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat


def test_string_literal_matching_synth_name_survives_reference_renaming():
    source = r'''(set-logic SLIA)
(synth-fun |"f"| () String ((Start String ("f"))))
(constraint (= |"f"| "f"))
(check-synth)'''
    translated = translate(source, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.sat

    negative = r'''(set-logic SLIA)
(synth-fun |"f"| () String ((Start String ("other"))))
(constraint (= |"f"| "f"))
(check-synth)'''
    translated = translate(negative, depth=0)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert check_z3(translated) == z3.unsat
