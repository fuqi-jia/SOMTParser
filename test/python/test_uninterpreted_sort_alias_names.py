import somtparser as sp


def test_free_sort_names_exclude_aliases_to_nullary_and_applied_constructors():
    parser = sp.Parser().parse_string(
        "(set-logic ALL)"
        "(declare-sort U 0)"
        "(declare-sort Box 1)"
        "(define-sort AliasU () U)"
        "(define-sort AliasBox () (Box Int))"
    )
    assert parser.uninterpreted_sorts == ["U", "Box"]


def test_parameter_history_does_not_hide_or_duplicate_later_free_sort():
    parser = sp.Parser().parse_string(
        "(set-logic ALL)"
        "(declare-datatype D (par (U) ((d (value U)))))"
        "(declare-sort U 0)"
    )
    assert parser.uninterpreted_sorts == ["U"]


def test_global_sort_survives_datatype_parameter_shadowing():
    parser = sp.Parser().parse_string(
        "(set-logic ALL)"
        "(declare-sort U 1)"
        "(declare-datatype D (par (U) ((d (value U)))))"
        "(declare-const x (U Int))"
    )
    assert parser.uninterpreted_sorts == ["U"]
