"""Compare exported constraints at the original public coordinates in tests."""
import json
import re

import z3


def private_witness_names(result):
    # Only an explicit lowering report authorizes hiding a coordinate. A user
    # symbol sharing the generated prefix stays free; prefix matching is unsafe.
    names = []
    formal = result.translation if callable(result.report) else result
    for choice in json.loads(formal.report.to_json())["choices"]:
        if (choice["unified_op"], choice["strategy"]) != (
                "positive-exists", "fresh-private-constant"):
            continue
        match = re.search(r" -> auxiliary '(!somt_exists_[0-9]+)';", choice["rationale"])
        assert match is not None, choice
        names.append(match.group(1))
    assert len(names) == len(set(names)), names
    return names


def public_relation(result, text=None, *, ctx=None):
    assertions = z3.parse_smt2_string(result.to_smt2() if text is None else text, ctx=ctx)
    body = z3.And(*assertions) if len(assertions) else z3.BoolVal(True, ctx=ctx)
    names = set(private_witness_names(result))
    if not names:
        return body
    witnesses, seen, pending = [], set(), [body]
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_quantifier(term):
            pending.append(term.body())
        elif z3.is_app(term):
            if (term.num_args() == 0 and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
                    and str(term.decl().name()) in names):
                witnesses.append(term)
            pending.extend(term.children())
    # Existential closure preserves every original assertion and leaves every
    # source coordinate free for the complete XOR comparison with the oracle.
    return z3.Exists(witnesses, body) if witnesses else body
