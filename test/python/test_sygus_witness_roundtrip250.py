"""End-to-end source witness reconstruction for the unbounded SyGuS encoding.

This test is intended to run against the separately staged 247 overlay. It
solves the target encoding, reads the generated String witness binding from
that target model, inserts the returned source term into the original
synth-fun signature, and checks the original constraint in an independent Z3
solver instance.
"""

import re

import z3
import somtparser as sp


_WITNESS_DECL = re.compile(
    r"\(declare-(?:const|fun)\s+(__somt_sygus_witness_text_0)\s+"
    r"(?:\(\)\s+)?String\)"
)
_DIRECT_VALUE_DECL = re.compile(
    r"\(declare-(?:const|fun)\s+(__somt_sygus_witness_value_0)\s+"
    r"(?:\(\)\s+)?(Int|Bool|String|\(_ BitVec \d+\))\)"
)


def _check(smt2):
    # Source witnesses use stable generated identifiers across independent
    # translations. Isolate each parse so Z3's global declaration context does
    # not make later tasks depend on test order.
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(smt2, ctx=ctx))
    result = solver.check()
    assert result != z3.unknown, solver.reason_unknown()
    return solver, result


def _target_source_witness(source):
    translated = sp.translate(source=source, language="sygus", profile="bmc",
                              options={"grammar_mode": "unbounded"})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    strategies = {choice.strategy for choice in translated.report.choices}
    assert strategies & {
        "unbounded-grammar-direct-constant",
        "unbounded-grammar-adt-recursive-evaluator",
    }

    # Pin the target dialect explicitly, and obtain the witness from a model
    # of the emitted target formula. For a single Constant root, the typed
    # model value is itself the exact source literal, avoiding a String/Int
    # renderer in the synthesis formula.
    target_smt = translated.to_smt2(sp.OmtDialect.Z3)
    target_solver, target_status = _check(target_smt)
    assert target_status == z3.sat
    direct = _DIRECT_VALUE_DECL.findall(target_smt)
    if direct:
        assert len(direct) == 1, direct
        name, sort = direct[0]
        if sort == "String":
            expression = z3.String(name, ctx=target_solver.ctx)
        elif sort == "Int":
            expression = z3.Int(name, ctx=target_solver.ctx)
        elif sort == "Bool":
            expression = z3.Bool(name, ctx=target_solver.ctx)
        else:
            width = int(re.search(r"BitVec (\d+)", sort).group(1))
            expression = z3.BitVec(name, width, ctx=target_solver.ctx)
        value = target_solver.model().eval(expression, model_completion=True)
        witness_term = value.sexpr()
        assert witness_term
        assert "__somt_sygus_render_" not in target_smt
        assert "str.replace_all" not in target_smt
        assert "str.from_int" not in target_smt
        return witness_term

    names = _WITNESS_DECL.findall(target_smt)
    assert len(names) == 1, names
    value = target_solver.model().eval(
        z3.String(names[0], ctx=target_solver.ctx), model_completion=True)
    assert z3.is_string_value(value), value
    witness_term = _decode_smt_string_value(value.sexpr())
    assert witness_term
    return witness_term


def _decode_smt_string_value(token):
    """Decode Z3's canonical SMT-LIB String literal, including Unicode escapes."""
    assert len(token) >= 2 and token[0] == token[-1] == '"', token
    result = []
    index = 1
    while index < len(token) - 1:
        char = token[index]
        if char == '"':
            assert index + 1 < len(token) - 1 and token[index + 1] == '"', token
            result.append('"')
            index += 2
        elif char == "\\":
            assert token.startswith(r"\u{", index), token[index:]
            end = token.find("}", index + 3)
            assert end >= 0, token[index:]
            result.append(chr(int(token[index + 3:end], 16)))
            index = end + 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def _check_reconstructed_definition(sort, witness_term, constraint):
    # SyGuS `(constraint ...)` is the source-side universal obligation for a
    # zero-argument function. Replacing synth-fun with this actual model term
    # and asserting the same formula checks its source meaning independently.
    source_smt = (
        "(set-logic ALL)\n"
        f"(define-fun f () {sort} {witness_term})\n"
        f"(assert {constraint})\n"
    )
    _, status = _check(source_smt)
    assert status == z3.sat, source_smt


def test_string_constant_witness_roundtrips_quotes_and_backslash():
    # SMT-LIB Unicode escapes are active in string literals. Encode the data
    # backslashes themselves so these source values contain literal \u0041 and
    # \u{41}, rather than the decoded character A. Include quotes and a plain
    # trailing backslash in the same witness.
    required_value = 'left' + chr(92) + 'u0041|mid' + chr(92) + 'u{41}|"quote"' + chr(92)
    required_literal = _source_string_token(required_value)
    source = (
        '(set-logic SLIA) '
        '(synth-fun f () String ((Start String ((Constant String))))) '
        f'(constraint (= f {required_literal})) (check-synth)'
    )
    witness = _target_source_witness(source)
    _check_reconstructed_definition("String", witness,
                                    f"(= f {required_literal})")


def _source_string_token(value):
    """SMT-LIB source token denoting `value`, without interpreting its slashes."""
    content = []
    for char in value:
        if char == chr(92):
            content.append(r"\u{5c}")
        elif char == '"':
            content.append('""')
        else:
            content.append(char)
    return '"' + ''.join(content) + '"'


def test_negative_integer_constant_witness_roundtrips_as_source_term():
    source = (
        '(set-logic LIA) '
        '(synth-fun f () Int ((Start Int ((Constant Int))))) '
        '(constraint (= f (- 17))) (check-synth)'
    )
    witness = _target_source_witness(source)
    _check_reconstructed_definition("Int", witness, "(= f (- 17))")


def test_bitvector_constant_witness_roundtrips_with_width():
    source = (
        '(set-logic BV) '
        '(synth-fun f () (_ BitVec 8) '
        ' ((Start (_ BitVec 8) ((Constant (_ BitVec 8)))))) '
        '(constraint (= f #xa5)) (check-synth)'
    )
    witness = _target_source_witness(source)
    _check_reconstructed_definition("(_ BitVec 8)", witness,
                                    "(= f #xa5)")
