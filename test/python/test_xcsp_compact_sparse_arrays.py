"""Compact scalar coordinates retain sparse domains, aliases, and group calls."""
from collections import defaultdict
import io

import pytest
from tools.validate_packed_smt_stream import commands, command_head, tokens
import somtparser as sp

z3 = pytest.importorskip("z3")


def _verify_factorized_relation(script, domains, coupled=None, unary=None):
    """Prove the whole conjunction through exhaustive syntactic partitioning.

    Every declaration and assertion is consumed. Unary factors are compared
    modulo a bijective renaming of their sole coordinate, for every coordinate;
    Z3 proves each distinct factor equivalent to its independently specified
    finite set. All factors mentioning multiple coordinates are checked jointly.
    Thus no global domain or group assertion is sampled or dropped, while Z3
    never receives the exponentially awkward XOR of 65,536 independent sets.
    """
    unary = unary or {}
    names = set(domains)
    declared = set()
    helpers = []
    helper_names = set()
    factors = defaultdict(list)
    shared = []
    shared_names = set()
    representative = "__test_domain_coordinate"
    assert representative not in names

    def render(items, rename=None):
        return " ".join(("|" + value.decode() + "|") if kind == "quoted"
                        else value.decode() for kind, value in
                        (("atom", representative.encode()) if rename is not None
                         and kind in ("atom", "quoted") and value.decode() == rename
                         else (kind, value) for kind, value in items))

    for command in commands(io.BytesIO(script.encode()), max_command_bytes=len(script.encode())):
        head, _ = command_head(command)
        ts = list(tokens(command.raw))
        if head in ("declare-fun", "declare-const"):
            name = ts[2][1].decode()
            assert name in names and name not in declared, name
            # These fixtures have only scalar Int observables, never functions.
            expected = [b"(", b"declare-fun", ts[2][1], b"(", b")", b"Int", b")"]
            if head == "declare-const":
                expected = [b"(", b"declare-const", ts[2][1], b"Int", b")"]
            assert [value for _, value in ts] == expected, command.raw
            declared.add(name)
        elif head == "define-fun":
            name = ts[2][1].decode()
            assert name not in names and name not in helper_names and name != representative
            assert not {value.decode() for kind, value in ts
                        if kind in ("atom", "quoted")} & names
            helper_names.add(name)
            helpers.append(command.raw.decode())
        elif head == "assert":
            assert not any(kind == "string" or (kind == "atom" and value in
                           (b"let", b"forall", b"exists", b"lambda"))
                           for kind, value in ts), command.raw
            support = {value.decode() for kind, value in ts
                       if kind in ("atom", "quoted") and value.decode() in names}
            assert support, command.raw  # No unaccounted constant/global factor.
            if len(support) == 1:
                name, = support
                factors[name].append(render(ts, name))
            else:
                shared.append(command.raw.decode())
                shared_names.update(support)
        else:
            assert head in ("set-logic", "check-sat", "exit"), command.raw
    assert declared == names
    assert set(factors) == names  # Includes all unused and terminal coordinates.
    prefix = "\n".join(helpers)
    context = z3.Context()
    # Definitions must be closed before the oracle injects its representative.
    assert len(z3.parse_smt2_string(prefix, ctx=context)) == 0
    value = z3.Int(representative, ctx=context)
    checked = set()
    for name in sorted(names):
        signature = tuple(sorted(factors[name]))
        members = tuple(domains[name])
        extra = unary.get(name)
        key = signature, members, extra
        if key in checked:
            continue
        checked.add(key)
        actual = z3.parse_smt2_string(prefix + "\n" + "\n".join(signature),
                                     decls={representative: value}, ctx=context)
        expected = z3.Or(*[value == member for member in members])
        if extra is not None:
            assert extra[0] == "ne"
            expected = z3.And(expected, value != extra[1])
        solver = z3.Solver(ctx=context)
        solver.set(timeout=20000)
        solver.add(z3.Xor(z3.And(*actual), expected))
        result = solver.check()
        assert result == z3.unsat, (name, result, solver.reason_unknown())
    assert set(unary) <= names
    variables = {name: z3.Int(name, ctx=context) for name in shared_names}
    actual_shared = z3.parse_smt2_string(prefix + "\n" + "\n".join(shared),
                                        decls=variables, ctx=context)
    expected_shared = (coupled(variables) if coupled is not None
                       else z3.BoolVal(True, ctx=context))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=20000)
    shared_formula = (z3.And(*actual_shared) if len(actual_shared)
                      else z3.BoolVal(True, ctx=context))
    solver.add(z3.Xor(shared_formula, expected_shared))
    result = solver.check()
    assert result == z3.unsat, (result, solver.reason_unknown())
    return len(declared), len(checked)


def _translate(source, tmp_path, file_input):
    if file_input:
        path = tmp_path / "sparse.xml"
        path.write_text(source, encoding="utf-8")
        result = sp.translate(path=str(path), language="xcsp3")
    else:
        result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.uses_packed_smt_stream
    return result


@pytest.mark.parametrize("file_input", [False, True])
def test_sparse_array_exact_relation_including_unused_cells_and_alias(tmp_path, file_input):
    source = '''<instance format="XCSP3" type="CSP"><variables>
      <array id="y" size="[256][256]" startIndex="5"> -1 1 </array>
      <var id="alias" as="y[5][5]"/>
      <var id="|__somt_xcsp_group_0|">-2..2</var>
      </variables><constraints>
      <group><intension>ne(%0,%1)</intension>
        <args>y[5][5] y[5][6]</args>
        <args>y[260][259] y[260][260]</args>
      </group></constraints></instance>'''
    result = _translate(source, tmp_path, file_input)
    assert result.report.stats.num_vars == 65538
    script = result.to_smt2()
    assert script.count("(declare-fun ") + script.count("(declare-const ") == 65538
    assert "(define-fun __somt_xcsp_group_0 " not in script
    domains = {f"y[{r}][{c}]": (-1, 1)
               for r in range(5, 261) for c in range(5, 261)}
    domains.update(alias=(-1, 1), __somt_xcsp_group_0=(-2, -1, 0, 1, 2))
    count, _ = _verify_factorized_relation(
        script, domains,
        lambda variables: z3.And(variables["y[5][5]"] != variables["y[5][6]"],
                                 variables["y[260][259]"] != variables["y[260][260]"]))
    assert count == 65538
    # The proven unary domain for alias permits either value independently;
    # a mistaken equality to y[5][5] would enter the shared XOR and fail above.


@pytest.mark.parametrize("text,members", [
    ("7 -5 7 2", [-5, 2, 7]),
    ("1 0 1", [0, 1]),
    ("-9223372036854775808 9223372036854775807", [-(2**63), 2**63-1]),
])
def test_explicit_finite_domains_keep_order_independent_exact_members(tmp_path, text, members):
    source = (f'<instance format="XCSP3" type="CSP"><variables>'
              f'<array id="a" size="[65536]">{text}</array>'
              '</variables></instance>')
    result = _translate(source, tmp_path, False)
    count, _ = _verify_factorized_relation(
        result.to_smt2(), {f"a[{i}]": tuple(members) for i in range(65536)})
    assert count == result.report.stats.num_vars == 65536


@pytest.mark.parametrize("file_input", [False, True])
def test_packed_sparse_membership_does_not_change_negated_group_constraint(tmp_path, file_input):
    source = '''<instance format="XCSP3" type="CSP"><variables>
      <array id="a" size="[65536]"> -3 3 </array>
      </variables><constraints><group><intension>not(eq(%0,3))</intension>
      <args>a[0]</args>
      <args>a[65535]</args></group></constraints></instance>'''
    result = _translate(source, tmp_path, file_input)
    count, _ = _verify_factorized_relation(
        result.to_smt2(), {f"a[{i}]": (-3, 3) for i in range(65536)},
        unary={"a[0]": ("ne", 3), "a[65535]": ("ne", 3)})
    assert count == 65536


@pytest.mark.parametrize("mutation", ["missing_first", "missing_last", "wrong_polarity"])
def test_factorized_oracle_rejects_changed_negated_group_calls(mutation):
    script = """(declare-const |a[0]| Int)(declare-const |a[1]| Int)
      (assert (or (= |a[0]| -3) (= |a[0]| 3)))
      (assert (or (= |a[1]| -3) (= |a[1]| 3)))"""
    if mutation != "missing_first":
        script += "(assert (not (= |a[0]| 3)))"
    if mutation != "missing_last":
        script += ("(assert (= |a[1]| 3))" if mutation == "wrong_polarity"
                   else "(assert (not (= |a[1]| 3)))")
    with pytest.raises(AssertionError):
        _verify_factorized_relation(
            script, {"a[0]": (-3, 3), "a[1]": (-3, 3)},
            unary={"a[0]": ("ne", 3), "a[1]": ("ne", 3)})


@pytest.mark.parametrize("mutation", ["missing_domain", "extra_domain", "wrong_last", "alias_tied", "missing_group"])
def test_factorized_oracle_rejects_relation_changes(mutation):
    declarations = "(declare-const |a[0]| Int)(declare-const |a[1]| Int)(declare-const alias Int)"
    first = "(assert (or (= |a[0]| -1) (= |a[0]| 1)))"
    last = "(assert (or (= |a[1]| -1) (= |a[1]| 1)))"
    alias = "(assert (or (= alias -1) (= alias 1)))"
    group = "(assert (distinct |a[0]| |a[1]|))"
    if mutation == "missing_domain":
        last = ""
    elif mutation == "extra_domain":
        last += "(assert (= |a[1]| 1))"
    elif mutation == "wrong_last":
        last = "(assert (or (= |a[1]| 0) (= |a[1]| 1)))"
    elif mutation == "alias_tied":
        group += "(assert (= alias |a[0]|))"
    else:
        group = ""
    with pytest.raises((AssertionError, KeyError)):
        _verify_factorized_relation(
            declarations + first + last + alias + group,
            {"a[0]": (-1, 1), "a[1]": (-1, 1), "alias": (-1, 1)},
            lambda v: v["a[0]"] != v["a[1]"])


def test_factorized_oracle_rejects_hidden_free_helper_symbol():
    source = """(declare-const a Int)
      (define-fun domain ((x Int)) Bool (= x __test_domain_coordinate))
      (assert (domain a))"""
    with pytest.raises(z3.Z3Exception):
        _verify_factorized_relation(source, {"a": (-1, 1)})


@pytest.mark.parametrize("body", ["(let ((a 1)) (= a 1))", "(forall ((a Int)) (= a a))"])
def test_factorized_oracle_rejects_bound_variable_assertions(body):
    with pytest.raises(AssertionError):
        _verify_factorized_relation("(declare-const a Int)(assert " + body + ")", {"a": (1,)})
