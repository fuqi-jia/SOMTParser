"""Ordered queries must remain replayable after scope and context changes."""
import pytest
import somtparser as sp


@pytest.mark.parametrize("logging", [False, True])
def test_assumptions_survive_pop_and_reset(logging):
    p = sp.Parser()
    p.set_command_logging(logging)
    p.parse_string("(push 2)(declare-const a Bool)"
                   "(check-sat-assuming (a (not a)))(pop 2)"
                   "(check-sat-assuming ())(reset)(check-sat)")
    queries = [c for c in p.script if c.type == sp.CmdType.CHECK_SAT_ASSUMING]
    assert [[v.to_smt2() for v in c.assumptions] for c in queries] == [["a", "(not a)"], []]
    assert queries[0].index == 2
    assert queries[0].original.strip() == "(check-sat-assuming (a (not a)))"
    assert p.assumptions == []
    assert p.script[-1].assumptions == []


def test_parsed_scope_depths_are_preserved_in_log():
    p = sp.Parser()
    p.set_command_logging(True)
    p.parse_string("(push 0)(push 3)(assert true)(pop 2)(pop 1)(check-sat)")
    scopes = [c for c in p.script if c.is_push or c.is_pop]
    assert [c.push_pop_level for c in scopes] == [0, 3, 2, 1]
    assert [c.index for c in scopes] == [0, 1, 3, 4]
    assert [c.original.strip() for c in scopes] == ["(push 0)", "(push 3)", "(pop 2)", "(pop 1)"]


def test_scope_api_commands_keep_monotonic_indices_with_parsed_commands():
    p = sp.Parser()
    p.set_command_logging(True)
    p.parse_string("(declare-const x Int)")
    p.push(2)
    p.parse_string("(check-sat-assuming ())")
    p.pop(2)
    p.reset_assertions()
    p.reset()
    p.parse_string("(check-sat)")
    assert [c.index for c in p.script] == list(range(7))


def test_dump_keeps_last_query_assumptions_after_pop():
    p = sp.Parser()
    p.parse_string("(declare-const a Bool)(declare-const b Bool)"
                   "(assert (not a))(assert b)(check-sat-assuming (a))"
                   "(push 1)(check-sat-assuming (b))(pop 1)")
    dumped = p.dump_smt2()
    assert "(check-sat-assuming (b))" in dumped
    q = sp.Parser().parse_string(dumped)
    assert [t.to_smt2() for t in q.script[-1].assumptions] == ["b"]


def test_dump_rejects_a_query_about_a_removed_local_declaration():
    p = sp.Parser()
    p.parse_string("(push 1)(declare-const local Bool)(check-sat-assuming (local))(pop 1)")
    with pytest.raises(RuntimeError, match="removed declaration"):
        p.dump_smt2()
    p.parse_string("(check-sat)")
    assert "(check-sat)" in p.dump_smt2()


@pytest.mark.parametrize("text", ["(pop 1)", "(push 1)(pop 2)", "(push -1)",
                                  "(push 1x)", "(push 1)(pop -1)", "(push 1)(pop 1x)"])
def test_invalid_scope_command_is_rejected(text):
    with pytest.raises(sp.ParseError):
        sp.Parser().parse_string(text)
