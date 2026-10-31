"""Server-only solver proof of every complete emitted derived-state relation."""
from pathlib import Path
import hashlib
import json
import sys
import z3
from z3.z3util import get_vars

root = Path(sys.argv[1])
seed, block, d, e, f = z3.Bools("seed block d e f")
x, defined = z3.Real("x"), z3.Bool("x_defined")
cases = {
    "relation0": z3.And(z3.Not(d), z3.Not(e)),
    "relation1": z3.And(z3.Not(d), z3.Not(e)),
    "relation2": z3.And(d == seed, e == seed),
    "relation3": z3.And(d == seed, e == seed, f == seed),
    "relation4": z3.And(d == z3.And(seed, z3.Not(block)), e == d),
    "relation5": d == z3.Or(seed, block),
    "relation6": z3.And(d == seed, e == seed),
    "relation7": z3.And(d == seed, e == z3.And(seed, block)),
    "symbol_collision": z3.And(d == seed, e == seed),
    "numeric_guard": z3.And(d == z3.And(defined, x >= z3.RealVal("1/3")), e == d),
}
rows = []
for name, expected in cases.items():
    path = root / (name + ".smt2")
    actual = z3.And(*z3.parse_smt2_file(str(path)))
    symbol_path = root / (name + ".symbols.json")
    symbols = json.loads(symbol_path.read_text())
    assert isinstance(symbols, list) and symbols
    by_source, by_target = {}, {}
    sorts = {"Bool": z3.BoolSort(), "Real": z3.RealSort()}
    for symbol in symbols:
        assert set(symbol) == {"source", "target", "sort", "auxiliary"}, symbol
        assert type(symbol["auxiliary"]) is bool
        source, target = symbol["source"], symbol["target"]
        assert isinstance(source, str) and isinstance(target, str)
        assert source not in by_source and target not in by_target, symbol
        assert symbol["sort"] in sorts, symbol
        by_source[source] = symbol
        by_target[target] = symbol
    substitutions = []
    for variable in get_vars(expected):
        symbol = by_source[str(variable)]
        assert not symbol["auxiliary"] and variable.sort() == sorts[symbol["sort"]]
        substitutions.append((variable, z3.Const(symbol["target"], variable.sort())))
    expected = z3.substitute(expected, *substitutions)
    auxiliaries = []
    for variable in get_vars(actual):
        symbol = by_target[str(variable)]
        assert variable.sort() == sorts[symbol["sort"]]
        if symbol["auxiliary"]:
            auxiliaries.append(variable)
    if name == "symbol_collision":
        assert by_source["e"]["target"] not in {"e", "e!0", "e!1"}
        assert by_source["e!0"]["target"] == "e!0"
        assert by_source["e!1"]["target"] == "e!1"
    projected = z3.Exists(auxiliaries, actual) if auxiliaries else actual
    solver = z3.Solver()
    solver.add(z3.Xor(projected, expected))
    result = solver.check()
    row = dict(case=name, full_relation=str(result), auxiliary_count=len(auxiliaries),
               target_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
               symbol_map_sha256=hashlib.sha256(symbol_path.read_bytes()).hexdigest(),
               source_target_symbols=symbols)
    if result != z3.unsat:
        row["counterexample"] = str(solver.model()) if result == z3.sat else solver.reason_unknown()
    rows.append(row)
    assert result == z3.unsat, row
    # A directly negated observation is always a genuine semantic mutation.
    target_d = z3.Bool(by_source["d"]["target"])
    mutation = z3.substitute(expected, (target_d, z3.Not(target_d)))
    check = z3.Solver()
    check.add(z3.Xor(projected, mutation))
    assert check.check() == z3.sat, name
(root / "derived-full-relations.json").write_text(json.dumps(
    dict(passed=True, cases=rows, limits=None, complete_relation_checks=len(rows)), indent=2) + "\n")
print(json.dumps(rows))
