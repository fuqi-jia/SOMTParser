"""Finite compiler-emitted set arrays preserve literals, aliases and carriers."""
import pytest
import somtparser as sp
import z3


def finite_set(*values):
    result = z3.EmptySet(z3.IntSort())
    for value in values:
        result = z3.SetAdd(result, z3.IntVal(value))
    return result


def cardinality_relation(count, variable, values, mode):
    relation = count == z3.Sum([z3.If(z3.IsMember(v, variable), 1, 0) for v in values])
    if mode == "reif":
        return z3.Bool("b") == relation
    if mode == "imp":
        return z3.Implies(z3.Bool("b"), relation)
    return relation


def cardinality_call(mode, operand="s"):
    suffix = "" if mode == "plain" else "_" + mode
    flag = "" if mode == "plain" else ",b"
    return "constraint set_card" + suffix + "(" + operand + ",n" + flag + ");"


def equivalent(source, expected, profile="default"):
    translated = sp.translate(source=source + "\nsolve satisfy;",
                              language="flatzinc", profile=profile,
                              dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.report.fidelity.sound
    assert translated.report.fidelity.complete
    script = translated.to_smt2(sp.OmtDialect.Z3)
    actual = z3.And(*z3.parse_smt2_string(script))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    return script


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_compiler_array_does_not_create_symbols_for_literals_or_parameters(profile):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    equivalent("set of int: p = {1,3}; set of int: q = p;"
               "var set of 1..3: s;"
               "array [1..7] of var set of int: a :: output_array([1..7]) "
               "= [{}, {1,3}, 1..2, p, q, s, s];"
               "constraint set_in(2,s);",
               z3.And(z3.IsSubset(s, finite_set(1,2,3)), z3.IsMember(2,s)), profile)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_bounded_array_intersects_alias_domains_without_retyping(profile):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    equivalent("var set of 1..4: s;"
               "array [1..3] of var set of {1,3}: a = [s,{1},s];",
               z3.IsSubset(s, finite_set(1,3)), profile)


@pytest.mark.parametrize("value", ["{}", "1..0", "{1,1,3}", "1..3"])
def test_fixed_arrays_introduce_no_decision_values(value):
    equivalent("array [1..1] of var set of int: a = [" + value + "];",
               z3.BoolVal(True))


@pytest.mark.parametrize("cell", ["{4}", "2..4", "p"])
def test_literal_and_parameter_cells_obey_the_array_carrier(cell):
    equivalent("set of int: p = {4};"
               "array [1..1] of var set of 1..3: a = [" + cell + "];",
               z3.BoolVal(False))


def test_bounded_array_can_declare_fresh_finite_element_names():
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    equivalent("array [1..2] of var set of {-2,4}: a = [s,s];",
               z3.IsSubset(s, finite_set(-2,4)))


def test_empty_compiler_array_is_a_complete_finite_array():
    equivalent("array [1..0] of var set of int: a = [];", z3.BoolVal(True))


def test_parameter_array_values_stay_fixed():
    equivalent("set of int: p = {1,3};"
               "array [1..2] of set of int: a = [p,{}];", z3.BoolVal(True))


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("mode", ["plain", "reif", "imp"])
@pytest.mark.parametrize("domain,values", [
    ("0..3", [0, 1, 2, 3]), ("{-2,4}", [-2, 4]), ("{}", []), ("1..0", []),
])
def test_declared_carrier_is_preserved_for_cardinality_export(profile, mode, domain, values):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    n = z3.Int("n")
    equivalent("var set of " + domain + ": s; var int: n; var bool: b;" + cardinality_call(mode),
               z3.And(z3.IsSubset(s, finite_set(*values)),
                      cardinality_relation(n, s, values, mode)), profile)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("mode", ["plain", "reif", "imp"])
def test_fresh_array_alias_retains_parameter_carrier_for_cardinality(profile, mode):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    equivalent("set of int: D = {-2,4};"
               "array [1..2] of var set of D: a = [s,s]; var int: n; var bool: b;"
               + cardinality_call(mode),
               z3.And(z3.IsSubset(s, finite_set(-2,4)),
                      cardinality_relation(z3.Int("n"), s, [-2,4], mode)), profile)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("mode", ["plain", "reif", "imp"])
def test_array_carrier_narrowing_remains_unconditional_when_cardinality_is_guarded(profile, mode):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    equivalent("var set of 1..4: s; array [1..1] of var set of {1,3}: a = [s];"
               "var int: n; var bool: b;" + cardinality_call(mode),
               z3.And(z3.IsSubset(s, finite_set(1,3)),
                      cardinality_relation(z3.Int("n"), s, [1,3], mode)), profile)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("mode", ["plain", "reif", "imp"])
def test_initialized_set_alias_keeps_its_resolved_symbol_carrier(profile, mode):
    s = z3.Const("s", z3.SetSort(z3.IntSort()))
    t = z3.Const("t", z3.SetSort(z3.IntSort()))
    equivalent("var set of {1,3}: s; var set of 1..4: t = s;"
               "array [1..2] of var set of int: a = [t,s]; var int: n; var bool: b;"
               + cardinality_call(mode, "t"),
               z3.And(z3.IsSubset(s, finite_set(1,3)), t == s,
                      cardinality_relation(z3.Int("n"), t, [1,2,3,4], mode)), profile)


@pytest.mark.parametrize("mode", ["plain", "reif", "imp"])
def test_fixed_parameter_cardinality_keeps_duplicate_set_members_extensional(mode):
    equivalent("set of int: p = {1,1,3}; var int: n; var bool: b;" + cardinality_call(mode, "p"),
               cardinality_relation(z3.Int("n"), finite_set(1,3), [1,3], mode))


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_actual_gt_sort_x47_cardinality_exports_with_its_63_element_carrier(profile):
    s = z3.Const("X_INTRODUCED_47_", z3.SetSort(z3.IntSort()))
    values = list(range(63))
    equivalent("var set of 0..62: X_INTRODUCED_47_; var int: X_INTRODUCED_158_;"
               "array [1..2] of var set of int: a = [X_INTRODUCED_47_,0..0];"
               "constraint set_card(X_INTRODUCED_47_,X_INTRODUCED_158_);",
               z3.And(z3.IsSubset(s, finite_set(*values)),
                      cardinality_relation(z3.Int("X_INTRODUCED_158_"), s, values, "plain")), profile)


@pytest.mark.parametrize("source", [
    "var set of int: s;",
    "var set of int: s = {1};",
    "array [1..1] of var set of int: a;",
    "array [1..1] of var set of int: a = [];",
    "array [1..0] of var set of int: a = [{}];",
    "array [1..2] of var set of int: a = [{}];",
    "array [1..1] of var set of int: a = [{},{}];",
    "array [2..2] of var set of int: a = [{}];",
    "array [int] of var set of int: a = [{}];",
    "array [1..-1] of var set of int: a = [];",
    "array [1..1] of var set of int: a = [{} ,];",
    "array [1..2] of var set of int: a = [{},,{}];",
    "array [1..1] of var set of int: a = [fresh];",
    "array [1..1] of var set of int: a = [true];",
    "array [1..1] of var set of int: a = [2];",
    "array [1..1] of var set of int: a = [{1,}];",
    "array [1..1] of var set of int: a = [{1.5}];",
    "array [1..1] of var set of int: a = [{true}];",
    "var int: x; array [1..1] of var set of int: a = [x];",
    "var bool: b; array [1..1] of var set of 1..3: a = [b];",
    "int: p = 1; array [1..1] of var set of int: a = [p];",
    "int: p = {1}; array [1..1] of var set of int: a = [p];",
    "set of int: p = q; set of int: q = p; "
    "array [1..1] of var set of int: a = [p];",
    "set of int: p = missing; array [1..1] of var set of 1..3: a = [p];",
    "var set of 1..3: s; set of int: p = s; "
    "array [1..1] of var set of int: a = [p];",
    "var set of 1..3: s; array [1..1] of set of int: a = [s];",
])
def test_incomplete_unbounded_or_mistyped_set_arrays_are_rejected(source):
    translated = sp.translate(source=source + " solve satisfy;", language="flatzinc")
    assert not translated.ok


def test_actual_gt_sort_output_array_keeps_all_fourteen_set_aliases():
    # Original first set-array declaration and the 14 scalar carriers it uses,
    # from Challenge 2025/gt-sort/n13_ub20_50.0_BEST.json (derived case 0035).
    # This isolates declaration semantics; it does not claim full-model proof.
    names = [47,48,49,50,51,52,53,61,62,63,64,75,76,89]
    symbols = [f"X_INTRODUCED_{i}_" for i in names]
    source = "".join(f"var set of 0..62: {name};" for name in symbols)
    cells = ["{0,19}","{0,17}","{0,17}","{0,13}","{0,12}","{0,11}",
             "{0,9}","{0,7}","{0,6}","{0,4}","{0,4}","{0,3}","0..1","0..0"]
    cells += symbols[:7] + ["0..0"]*7 + symbols[7:11] + ["0..0"]*4
    cells += ["1..0"]*6 + symbols[11:13] + ["1..0"]*12
    cells += symbols[13:] + ["1..0"]*13
    assert len(cells) == 70
    source += ("array [1..70] of var set of int: X_INTRODUCED_32_"
               " :: output_array([1..70]) = [" + ",".join(cells) + "];")
    carrier = finite_set(*range(63))
    equivalent(source, z3.And(*[z3.IsSubset(z3.Const(name, z3.SetSort(z3.IntSort())), carrier)
                               for name in symbols]))


def reified(mode, relation):
    if mode == "_reif":
        return z3.Bool("b") == relation
    if mode == "_imp":
        return z3.Implies(z3.Bool("b"), relation)
    return relation


@pytest.mark.parametrize("name", ["array_set_element", "array_var_set_element"])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_set_element_full_relation_includes_index_partiality(name, mode, profile):
    carrier = finite_set(0,1,2)
    r, s = z3.Consts("r s", z3.SetSort(z3.IntSort()))
    i = z3.Int("i")
    source = "set of int: p = {2}; var int: i; var set of 0..2: r;"
    base = [z3.IsSubset(r, carrier)]
    if name == "array_set_element":
        source += "array [1..3] of set of int: a = [{},1..2,p];"
        values = [finite_set(), finite_set(1,2), finite_set(2)]
    else:
        source += "var set of 0..2: s; array [1..3] of var set of int: a = [s,{1},p];"
        base.append(z3.IsSubset(s, carrier))
        values = [s, finite_set(1), finite_set(2)]
    if mode:
        source += "var bool: b;"
    source += f"constraint {name}{mode}(i,a,r" + (",b" if mode else "") + ");"
    # Enumerate the exact 1-based relation independently of the emitted ITE.
    # For every out-of-range index the relation is false, including when its
    # false value is observed through reification or an inactive implication.
    relation = z3.Or(*[z3.And(i == k, r == value)
                       for k, value in enumerate(values, 1)])
    equivalent(source, z3.And(*base, reified(mode, relation)), profile)


@pytest.mark.parametrize("index", [0, -1, 4])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_out_of_range_set_element_reifies_the_entire_false_relation(index, mode):
    source = "var bool: b;" if mode else ""
    source += (f"constraint array_var_set_element{mode}({index},[{{}},{{1}},{{2}}],{{}}"
               + (",b" if mode else "") + ");")
    equivalent(source, reified(mode, z3.BoolVal(False)))


@pytest.mark.parametrize("name", ["array_set_element", "array_var_set_element"])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_empty_set_element_array_has_the_false_relation(name, mode):
    source = "var int: i;" + ("var bool: b;" if mode else "")
    source += f"constraint {name}{mode}(i,[],{{}}" + (",b" if mode else "") + ");"
    equivalent(source, reified(mode, z3.BoolVal(False)))


@pytest.mark.parametrize("prefix,args", [
    ("", "1.5,[],{}"), ("", "true,[],{}"), ("", "1,[],1"),
    ("array [1..0] of int: a = [];", "1,a,{}"),
])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_empty_set_element_does_not_hide_wrong_argument_types(prefix, args, mode):
    source = prefix + ("var bool: b;" if mode else "")
    source += f"constraint array_var_set_element{mode}({args}" + (",b" if mode else "") + ");"
    result = sp.translate(source=source + " solve satisfy;", language="flatzinc")
    assert not result.ok


@pytest.mark.parametrize("args", [
    "true,[{1}],{1}", "1.5,[{1}],{1}", "{1},[{1}],{1}",
    "1,[1],{1}", "1,[true],{1}", "1,[{1}],1", "1,[{1}],true",
    "1,[missing],{1}",
])
def test_set_element_rejects_wrong_index_cell_and_result_types(args):
    result = sp.translate(source=f"constraint array_var_set_element({args}); solve satisfy;",
                          language="flatzinc")
    assert not result.ok


def test_actual_gt_sort_first_set_element_call_has_the_full_fourteen_way_relation():
    values = [(0,19),(0,17),(0,17),(0,13),(0,12),(0,11),(0,9),
              (0,7),(0,6),(0,4),(0,4),(0,3),(0,1),(0,)]
    cells = ["{0,19}","{0,17}","{0,17}","{0,13}","{0,12}","{0,11}",
             "{0,9}","{0,7}","{0,6}","{0,4}","{0,4}","{0,3}","0..1","0..0"]
    source = ("var 1..14: X_INTRODUCED_104_ ::var_is_introduced;"
              "var set of 0..19: X_INTRODUCED_222_ ::var_is_introduced :: is_defined_var;"
              "array [1..14] of var set of int: X_INTRODUCED_217_ ::var_is_introduced = ["
              + ",".join(cells) + "];"
              "constraint array_var_set_element(X_INTRODUCED_104_,X_INTRODUCED_217_,"
              "X_INTRODUCED_222_) :: defines_var(X_INTRODUCED_222_);")
    index = z3.Int("X_INTRODUCED_104_")
    result = z3.Const("X_INTRODUCED_222_", z3.SetSort(z3.IntSort()))
    relation = z3.Or(*[z3.And(index == k, result == finite_set(*value))
                       for k, value in enumerate(values, 1)])
    equivalent(source, z3.And(index >= 1, index <= 14,
                             z3.IsSubset(result, finite_set(*range(20))), relation))
