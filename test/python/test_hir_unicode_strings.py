"""Unicode String HIR export checked against direct escaped SMT-LIB."""
import shutil
import subprocess

import pytest
import z3

from somtparser.hir import HirBuilder


def lit(value, sort="String"):
    return {"literal": value, "sort": sort}


def op(name, *args):
    return {"op": name, "args": list(args)}


CLAIMS = [
    (
        op("not", op("str.contains", lit("é"), lit("e9"))),
        r'(not (str.contains "\u{e9}" "e9"))',
    ),
    (
        op("not", op("str.contains", lit('A"B\\Cé'), lit(r"\u{e9}"))),
        r'(not (str.contains "A""B\u{5c}C\u{e9}" "\u{5c}u{e9}"))',
    ),
    (
        op("eq", op("str.++", lit('A"B\\C'), lit("é")), lit('A"B\\Cé')),
        r'(= (str.++ "A""B\u{5c}C" "\u{e9}") "A""B\u{5c}C\u{e9}")',
    ),
    (
        op("eq", op("str.len", lit('A"B\\Cé')), lit(6, "Int")),
        r'(= (str.len "A""B\u{5c}C\u{e9}") 6)',
    ),
    (
        op("eq", op("str.len", lit("é")), lit(2, "Int")),
        r'(= (str.len "e\u{301}") 2)',
    ),
    (
        op("eq", op("str.at", lit("café"), lit(3, "Int")), lit("é")),
        r'(= (str.at "caf\u{e9}" 3) "\u{e9}")',
    ),
    (
        op("eq", op("str.substr", lit("café"), lit(2, "Int"), lit(2, "Int")), lit("fé")),
        r'(= (str.substr "caf\u{e9}" 2 2) "f\u{e9}")',
    ),
    (
        op("eq", op("str.indexof", lit("café"), lit("é"), lit(0, "Int")), lit(3, "Int")),
        r'(= (str.indexof "caf\u{e9}" "\u{e9}" 0) 3)',
    ),
    (
        op("str.contains", lit("café"), lit("é")),
        r'(str.contains "caf\u{e9}" "\u{e9}")',
    ),
    (
        op("not", op("str.contains", lit("café"), lit("Ã©"))),
        r'(not (str.contains "caf\u{e9}" "\u{c3}\u{a9}"))',
    ),
    (
        op("str.prefixof", lit("é"), lit("éclair")),
        r'(str.prefixof "\u{e9}" "\u{e9}clair")',
    ),
    (
        op("str.suffixof", lit("é"), lit("café")),
        r'(str.suffixof "\u{e9}" "caf\u{e9}")',
    ),
    (
        op("eq", op("str.replace", lit("café"), lit("é"), lit("é")), lit("café")),
        r'(= (str.replace "caf\u{e9}" "\u{e9}" "e\u{301}") "cafe\u{301}")',
    ),
    (
        op(
            "str.in_re",
            lit("é"),
            op("re.range", lit("é"), lit("ê")),
        ),
        r'(str.in_re "\u{e9}" (re.range "\u{e9}" "\u{ea}"))',
    ),
    (
        op(
            "not",
            op("str.in_re", lit("éx"), op("re.range", lit("é"), lit("ê"))),
        ),
        r'(not (str.in_re "\u{e9}x" (re.range "\u{e9}" "\u{ea}")))',
    ),
    (
        op(
            "not",
            op("str.in_re", lit("x"), op("re.range", lit("éx"), lit("ê"))),
        ),
        r'(not (str.in_re "x" (re.range "\u{e9}x" "\u{ea}")))',
    ),
    (
        op("str.in_re", lit("café"), op("str.to_re", lit("café"))),
        r'(str.in_re "caf\u{e9}" (str.to_re "caf\u{e9}"))',
    ),
]


def build_hir(negated=False):
    builder = HirBuilder()
    relation = op("and", *(claim for claim, _ in CLAIMS))
    builder.constrain(op("not", relation) if negated else relation)
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result.to_smt2()


def reference_smt(negated=False, portable=False):
    conjunction = "(and " + " ".join(reference for _, reference in CLAIMS) + ")"
    if portable:
        # UnicodeStrings specifies the empty language for this multi-character
        # endpoint. cvc5 1.3.1 rejects its original spelling during parsing.
        # Keep the original below for the independent Z3 equivalence check.
        conjunction = conjunction.replace(
            r'(re.range "\u{e9}x" "\u{ea}")', 're.none')
    formula = f"(not {conjunction})" if negated else conjunction
    return f"(set-logic ALL)\n(assert {formula})\n"


def z3_status(script):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(*z3.parse_smt2_string(script))
    return solver.check()


def cvc5_status(script):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for the independent Unicode string oracle")
    if "(check-sat)" not in script:
        script += "\n(check-sat)\n"
    result = subprocess.run(
        [executable, "--lang=smt2", "--tlimit=5000"],
        input=script,
        text=True,
        capture_output=True,
        timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout + result.stderr
    return answers[0]


def test_unicode_string_operators_match_escaped_reference_in_both_solvers():
    exported = build_hir()
    # The supported SMT-LIB transport uses codepoint escapes for non-ASCII
    # text and the standard doubled-quote form for embedded quotation marks.
    assert r"\u{e9}" in exported
    assert r"\u{301}" in exported
    assert r"\u{5c}" in exported
    assert "é" not in exported

    exported_negative = build_hir(negated=True)
    expected_status = {False: z3.sat, True: z3.unsat}
    for negative in (False, True):
        reference = reference_smt(negated=negative)
        hir_output = exported_negative if negative else exported
        want = expected_status[negative]
        assert z3_status(reference) == want
        assert z3_status(hir_output) == want
        cvc5_want = "sat" if want == z3.sat else "unsat"
        portable_reference = reference_smt(negated=negative, portable=True)
        original_formula = z3.And(*z3.parse_smt2_string(reference))
        portable_formula = z3.And(*z3.parse_smt2_string(portable_reference))
        comparison = z3.Solver()
        comparison.add(z3.Xor(original_formula, portable_formula))
        assert comparison.check() == z3.unsat
        assert cvc5_status(portable_reference) == cvc5_want
        assert cvc5_status(hir_output) == cvc5_want


@pytest.mark.parametrize('lo,hi', [
    ('', 'z'), ('éx', 'ê'), ('é', 'êx'), ('e\u0301', 'z'),
    ('ê', 'é'), ('é', 'a'), ('😀', 'é'),
])
def test_empty_unicode_ranges_load_in_both_solvers(lo, hi):
    builder = HirBuilder()
    builder.declare('word', 'String')
    builder.constrain(op('str.in_re', {'var': 'word'}, op('re.range', lit(lo), lit(hi))))
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert z3_status(script) == z3.unsat
    assert cvc5_status(script) == 'unsat'


@pytest.mark.parametrize('symbolic_first', [False, True])
def test_non_singleton_endpoint_makes_symbolic_range_empty(symbolic_first):
    builder = HirBuilder()
    builder.declare('endpoint', 'String')
    builder.declare('word', 'String')
    endpoints = [{'var': 'endpoint'}, lit('éx')]
    if not symbolic_first:
        endpoints.reverse()
    builder.constrain(op('str.in_re', {'var': 'word'}, op('re.range', *endpoints)))
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert z3_status(script) == z3.unsat
    assert cvc5_status(script) == 'unsat'


@pytest.mark.parametrize('word,expected', [('a', True), ('z', True), ('é', True), ('ê', False)])
def test_unicode_range_crossing_ascii_boundary(word, expected):
    builder = HirBuilder()
    builder.constrain(op('str.in_re', lit(word), op('re.range', lit('a'), lit('é'))))
    translated = builder.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    assert z3_status(script) == (z3.sat if expected else z3.unsat)
    assert cvc5_status(script) == ('sat' if expected else 'unsat')
