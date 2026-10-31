"""The compact selector circuit preserves bounded grammar semantics."""

import z3
import somtparser as sp


def _translation(source, depth=1):
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": str(depth)})
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return result


def _translate(source, depth=1):
    return _translation(source, depth).to_smt2()


def _status(smt2, string_input=None):
    solver = z3.Solver()
    solver.set(timeout=10000)
    assertions = z3.parse_smt2_string(smt2)
    solver.add(assertions)
    if string_input is not None:
        # Keep every original assertion and add an implied instance of each
        # String grammar equation at the input used by the source constraint.
        # Quantified String synthesis may otherwise return unknown even for
        # the simple impossible length below; no selector is fixed here.
        instances = [z3.substitute_vars(term.body(), z3.StringVal(string_input))
                     for term in assertions
                     if z3.is_quantifier(term) and term.is_forall()
                     and term.num_vars() == 1
                     and term.var_sort(0) == z3.StringSort()]
        assert instances
        solver.add(instances)
    result = solver.check()
    assert result != z3.unknown
    return result


def _assert_fixed_string_witness(smt2, body):
    # Instantiate a concrete total function and every production selector in
    # the actual emitted formula. This preserves every assertion while
    # avoiding incompleteness of quantified String-function synthesis in Z3.
    formula = z3.And(*z3.parse_smt2_string(smt2))
    declarations, pending, seen = {}, [formula], set()
    while pending:
        expr = pending.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if z3.is_quantifier(expr):
            pending.append(expr.body())
        elif z3.is_app(expr):
            if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                declarations[str(expr.decl().name())] = expr.decl()
            pending.extend(expr.children())
    function = declarations["__somt_sygus_function_0"]
    assert function.arity() == 1 and function.domain(0) == z3.StringSort()
    selectors = [decl() for name, decl in declarations.items()
                 if name.startswith("__somt_sygus_grammar_select_")]
    assert selectors
    instantiated = z3.substitute_funs(formula, (function, body))
    instantiated = z3.substitute(instantiated, *[(s, z3.IntVal(0)) for s in selectors])
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.simplify(instantiated))
    assert solver.check() == z3.sat


def _product_grammar(constraint):
    # 2**13 distinct derivations are represented by 13 independent child
    # selectors, without materializing their Cartesian product.
    conjunction = " ".join(["B"] * 13)
    return ("(set-logic LIA) "
            "(synth-fun f () Bool "
            "((Start Bool ((and " + conjunction + "))) "
            " (B Bool (true false)))) "
            "(constraint " + constraint + ") (check-synth)")


def test_large_product_uses_small_selector_circuit_and_remains_satisfiable():
    translated = _translation(_product_grammar("f"))
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    smt2 = translated.to_smt2()
    assert len(smt2) < 20000
    assert _status(smt2) == z3.sat


def test_selectors_are_fixed_across_all_universal_inputs():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(synth-fun f ((x Int)) Bool "
              "((Start Bool ((and " + " ".join(["B"] * 7) + "))) "
              " (B Bool (true false (= x 0) (= x 1))))) "
              "(constraint (= (f g) (and (<= 0 g) (<= g 1)))) "
              "(check-synth)")
    # No single grammar term equals this predicate for every integer. If the
    # production selector were accidentally inside forall g, the formula
    # would become satisfiable by choosing a different rule per input.
    assert _status(_translate(source, depth=1)) == z3.unsat


def test_compact_candidate_helper_captures_remain_universal():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g 0)) "
              "(synth-fun f () Bool "
              "((Start Bool ((and " + " ".join(["B"] * 8) + "))) "
              " (B Bool (base true false)))) "
              "(constraint (= f base)) (check-synth)")
    # `base` is a legal grammar terminal but varies with the source universal;
    # no one fixed synthesized term can equal it for every g.
    assert _status(_translate(source, depth=1)) == z3.unsat


def test_compact_captured_helper_target_encoding_is_satisfiable():
    source = ("(set-logic LIA) (declare-var g Int) "
              "(define-fun base () Bool (= g g)) "
              "(synth-fun f () Bool "
              "((Start Bool ((and " + " ".join(["B"] * 13) + "))) "
              " (B Bool (base false)))) "
              "(constraint f) (check-synth)")
    translated = _translation(source, depth=1)
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    # Every selector may choose the true source helper. Its target closure
    # must remain valid and satisfiable for all values of g.
    assert _status(translated.to_smt2()) == z3.sat


def test_compact_target_only_helper_alias_encoding_is_satisfiable():
    children = " ".join(["B"] * 13)
    source = ("(set-logic LIA) "
              "(define-fun int.to.str ((x Int)) Bool (= x 0)) "
              "(synth-fun f () Bool "
              "((Start Bool ((and " + children + "))) "
              " (B Bool ((int.to.str 0) false)))) "
              "(constraint f) (check-synth)")
    translated = _translation(source, depth=1)
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    smt2 = translated.to_smt2()
    assert "__somt_sygus_source_helper_" in smt2
    assert _status(smt2) == z3.sat


def test_compact_repeated_nonterminal_occurrences_choose_independently():
    # The xor needs distinct choices at the two B occurrences: true xor
    # (= x 0) equals not (= x 0). Thirteen C fillers force the Cartesian
    # product above the enumerator threshold without changing that condition.
    source = ("(set-logic LIA) (declare-var g Int) "
              "(synth-fun f ((x Int)) Bool "
              "((Start Bool ((and (xor B B) " + " ".join(["C"] * 13) + "))) "
              " (B Bool (true (= x 0))) (C Bool (true false)))) "
              "(constraint (= (f g) (not (= g 0)))) (check-synth)")
    translated = _translation(source, depth=1)
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    smt2 = translated.to_smt2()
    assert len(smt2) < 50000
    assert _status(smt2) == z3.sat


def test_configured_depth_is_not_silently_increased():
    source = ("(set-logic LIA) "
              "(synth-fun f () Bool "
              "((Start Bool (B)) (B Bool (true)))) "
              "(constraint f) (check-synth)")
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": "0"})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert _status(result.to_smt2()) == z3.unsat
    assert any(choice.strategy == "empty-bounded-grammar"
               for choice in result.report.choices)
    assert _status(_translation(source, depth=1).to_smt2()) == z3.sat


def test_compact_string_literal_is_not_resolved_as_a_nonterminal():
    concat = "(str.++ " + " ".join(["B"] * 13) + ")"
    source = ("(set-logic SLIA) "
              "(synth-fun f () String "
              "((Start String (\"x\" " + concat + ")) "
              "(|\"x\"| String (\"other\")) "
              "(B String (\"a\" \"b\")))) "
              "(constraint (= f \"x\")) (check-synth)")
    # The literal "x" and quoted nonterminal |"x"| have the same decoded
    # spelling. Only the latter is a nonterminal reference; the exact literal
    # keeps this bounded grammar satisfiable.
    translated = _translation(source, depth=1)
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    smt2 = translated.to_smt2()
    assert _status(smt2) == z3.sat


def test_compact_variable_string_uses_quoted_parameter_symbol():
    concat = "(str.++ (Variable String) " + " ".join(["B"] * 13) + ")"
    source = ("(set-logic SLIA) "
              "(synth-fun f ((|true| String)) String "
              "((Start String (" + concat + ")) "
              " (B String (\"a\" \"b\")))) "
              "(constraint (= (f \"x\") \"xaaaaaaaaaaaaa\")) (check-synth)")
    # The reserved-word parameter is a String variable. Rendering its decoded
    # name as the bare token true would turn it into a Bool literal.
    _assert_fixed_string_witness(
        _translate(source, depth=1),
        z3.Concat(z3.Var(0, z3.StringSort()), z3.StringVal("a" * 13)),
    )
    # Thirteen nonempty children cannot disappear from the concatenation.
    impossible = source.replace('"xaaaaaaaaaaaaa"', '"x"')
    assert _status(_translate(impossible, depth=1), string_input="x") == z3.unsat


def test_compact_grammar_prefix_quotes_synth_function_name():
    source = ("(set-logic LIA) "
              "(synth-fun |odd function| () Bool "
              "((Start Bool ((and " + " ".join(["B"] * 13) + "))) "
              " (B Bool (true false)))) "
              "(constraint |odd function|) (check-synth)")
    assert _status(_translate(source, depth=1)) == z3.sat


def test_compact_string_operator_alias_is_normalized_in_target_formula():
    sum_term = "(+ " + " ".join(["B"] * 13) + ")"
    source = ("(set-logic SLIA) "
              "(synth-fun f ((s String)) Int "
              "((Start Int ((str.to.int s) " + sum_term + ")) "
              " (B Int (0 1)))) "
              "(constraint (= (f \"123\") 123)) (check-synth)")
    smt2 = _translate(source, depth=1)
    assert "str.to_int" in smt2
    _assert_fixed_string_witness(smt2, z3.StrToInt(z3.Var(0, z3.StringSort())))


def test_sparse_deep_grammar_uses_budgeted_circuit_without_changing_depth():
    # There is exactly one derivation: each nonterminal refers to the next,
    # and the final production is true. Estimating every (nonterminal, depth)
    # state would exceed the existing 100,000 circuit-work budget long before
    # reaching this derivation, so the explicit circuit worklist must take
    # over without materializing candidates or recursing down the chain.
    count = 1200
    declarations = " ".join(
        f"(N{i} Bool)" for i in range(count)
    )
    rules = " ".join(
        f"(N{i} Bool ({'N' + str(i + 1) if i + 1 < count else 'true'}))"
        for i in range(count)
    )
    source = ("(set-logic LIA) (synth-fun f () Bool ("
              + declarations + ") (" + rules + ")) "
              "(constraint f) (check-synth)")

    translated = _translation(source, depth=count - 1)
    assert any(choice.strategy == "bounded-grammar-selector-circuit"
               for choice in translated.report.choices)
    smt2 = translated.to_smt2()
    assert _status(smt2) == z3.sat

    too_shallow = sp.translate(source=source, language="sygus", profile="bmc",
                               options={"grammar_depth": str(count - 2)})
    assert too_shallow.ok, [d.message for d in too_shallow.diagnostic_items]
    assert _status(too_shallow.to_smt2()) == z3.unsat
    assert any(choice.strategy == "empty-bounded-grammar"
               for choice in too_shallow.report.choices)
